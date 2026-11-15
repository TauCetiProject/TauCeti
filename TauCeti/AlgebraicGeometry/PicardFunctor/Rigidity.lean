/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Automorphisms
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf

/-!
# Rigidity of the rigidified Picard functor

Let `f : X ⟶ S` be a morphism of schemes with a section `x₀`, and let `T` be a scheme over `S`.
The objects of the rigidified Picard functor of `(X, x₀)` at `T` are line bundles on
`X_T = T ×_S X` rigidified along the base-changed section `x₀_T`. A rigidified line bundle has no
automorphisms other than the identity once every global function on `X_T` is pulled back from
`T`. This holds when `f` is quasi-compact and quasi-separated with `f_* 𝒪_X = 𝒪_S` and `T` is flat
over `S`, because `f_* 𝒪_X = 𝒪_S` is stable under flat base change
(`TauCeti.AlgebraicGeometry.isIso_app_pullback_fst_of_flat`).

Over a field every scheme is flat, so for a proper integral scheme `X` over a field `K` with a
`K`-rational point `x₀`, line bundles on `X_T` rigidified along `x₀_T` have no nontrivial
automorphisms for every scheme `T` over `K`. This is the setting of the Jacobian of a curve, where
it means that an isomorphism between two objects of the rigidified Picard functor is unique when
it exists.

## Main results

* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle.autSubgroup_eq_bot_of_flat`: rigidity over a
  flat base change, when `f` is quasi-compact and quasi-separated with `f_* 𝒪_X = 𝒪_S`;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle.autSubgroup_eq_bot_of_universallyClosed`:
  rigidity over every base change, for a proper (more generally, universally closed and
  quasi-separated) integral scheme over a field with a rational point.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

namespace RigidifiedLineBundle

/-- **Rigidity over a flat base change.** Let `f : X ⟶ S` be quasi-compact and quasi-separated
with `f_* 𝒪_X = 𝒪_S`, and let `x₀` be a section of `f`. For every scheme `T` flat over `S`, a line
bundle on `T ×_S X` rigidified along the base-changed section has no automorphisms other than the
identity. -/
theorem autSubgroup_eq_bot_of_flat {S X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (hf : ∀ V : S.affineOpens, IsIso (f.app V)) (x₀ : S ⟶ X)
    (hx₀ : x₀ ≫ f = 𝟙 S) (T : Over S) [Flat T.hom]
    (P : RigidifiedLineBundle (baseChangeSection f x₀ hx₀ T)) : P.autSubgroup = ⊥ := by
  have := isIso_app_pullback_fst_of_flat f T.hom hf ⊤
  exact P.autSubgroup_eq_bot_of_comp_eq_id (baseChangeSection_fst f x₀ hx₀ T)
    ((ConcreteCategory.isIso_iff_bijective _).mp this).2

/-- **Rigidity for a proper integral scheme with a rational point.** Let `X` be integral,
universally closed and quasi-separated over a field `K` (for instance proper), with a `K`-rational
point `x₀`. For every scheme `T` over `K`, a line bundle on `T ×_K X` rigidified along the
base-changed point has no automorphisms other than the identity. -/
theorem autSubgroup_eq_bot_of_universallyClosed {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f] [QuasiSeparated f]
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 (Spec (.of K))) (T : Over (Spec (.of K)))
    (P : RigidifiedLineBundle (baseChangeSection f x₀ hx₀ T)) : P.autSubgroup = ⊥ := by
  have := isIso_app_pullback_fst_of_section f hx₀ T.hom ⊤
  exact P.autSubgroup_eq_bot_of_comp_eq_id (baseChangeSection_fst f x₀ hx₀ T)
    ((ConcreteCategory.isIso_iff_bijective _).mp this).2

end RigidifiedLineBundle

end AlgebraicGeometry

end TauCeti
