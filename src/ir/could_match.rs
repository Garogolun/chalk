use errors::*;
use ir::*;
use zip::{Zip, Zipper};

/// A fast check to see whether two things could ever possibly match.
pub trait CouldMatch<T> {
    fn could_match(&self, other: &T) -> bool;
}

impl<T: Zip> CouldMatch<T> for T {
    fn could_match(&self, other: &T) -> bool {
        return Zip::zip_with(&mut MatchZipper, self, other).is_ok();

        struct MatchZipper;

        impl Zipper for MatchZipper {
            fn zip_tys(&mut self, a: &Ty, b: &Ty) -> Result<()> {
                let could_match = match (a, b) {
                    (&Ty::Apply(ref a), &Ty::Apply(ref b)) => {
                        a.name == b.name &&
                            a.parameters.iter()
                                        .zip(&b.parameters)
                                        .all(|(p_a, p_b)| p_a.could_match(p_b))
                    }

                    _ => true,
                };

                if could_match { Ok(()) } else { Err(Error::from_kind(ErrorKind::CouldNotMatch)) }
            }

            fn zip_lifetimes(&mut self, _: &Lifetime, _: &Lifetime) -> Result<()> {
                Ok(())
            }
        }
    }
}

impl CouldMatch<DomainGoal> for ProgramClause {
    fn could_match(&self, other: &DomainGoal) -> bool {
        self.implication.value.consequence.could_match(other)
    }
}

