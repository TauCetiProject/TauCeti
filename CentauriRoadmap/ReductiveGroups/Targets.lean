import Mathlib

/-!
# Reductive algebraic groups: target signatures

The narrative roadmap (the three "paved" models, the layer-by-layer build plan
Layers 0–7, the worked examples, and the references) is in `README.md`. We build the
whole tower here rather than waiting on Mathlib.

This file holds the **Layer 0** targets translating between affine group schemes and
Hopf algebras (Kevin Buzzard). They elaborate against the pinned Mathlib commit and are
stated with `sorry` (allowed in this human-owned roadmap library). As later layers
make their types expressible in `Centauri/`, add their milestones here with `sorry`
and hand them to the AIs to discharge. Next up after these: the convolution group
structure on the functor of points, and base change of Hopf algebras.
-/

open CategoryTheory AlgebraicGeometry CommRingCat Scheme Opposite Spec
open scoped SpecOfNotation

namespace CentauriRoadmap.ReductiveGroups

universe u

variable (R : Type u) [CommRing R]

/-- `Γ(G)` is an `R`-Hopf algebra, for `G` an affine group scheme over `Spec R`. -/
example (G : Scheme) (φ : G ⟶ Spec(R)) [GrpObj (Over.mk φ)] [IsAffine G] :
    HopfAlgebra R (Γ.obj (op G)) := sorry

/-- The affine group scheme `Spec A` over `Spec R` associated to a Hopf algebra `A`. -/
example (A : Type u) [CommRing A] [HopfAlgebra R A] :
    GrpObj (Over.mk (map (ofHom (algebraMap R A)) : Spec(A) ⟶ Spec(R))) := sorry

end CentauriRoadmap.ReductiveGroups
