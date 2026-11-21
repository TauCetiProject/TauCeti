/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.RingTheory.LocalRing.RingHom
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Morphisms from affine schemes restricted to a punctured spectrum

Let `A` be a Noetherian local ring of depth at least two and `U` its punctured spectrum.
An affine `U`-scheme `V` is the restriction of `Spec Γ(V, 𝒪_V)`. If an `A`-algebra `B` is
recovered from the global functions on `Spec B ×_{Spec A} U`, maps from this restriction
to `V` over `U` correspond to `A`-algebra maps `Γ(V, 𝒪_V) → B`.

The comparison is natural in the test algebra `B`, so restriction to a thickening on the
source is described by composition with the corresponding quotient map. If `A` has depth at
least three and `a` is a nonzerodivisor, the test algebras `B/aⁿB` all satisfy the required
extension property for functions when `B` is flat over `A`. The depth bound gives Hartogs on
`A/(aⁿ)` even though `B/aⁿB` need not be flat over `A`.

Together these results translate the morphism comparison in the local Lefschetz extension
problem into an adic lifting problem for algebra maps.

## References

* [The Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM), the local
  Lefschetz extension problem.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open scoped Pointwise

universe u

namespace TauCeti.IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The affine hull over `Spec A` of an affine scheme over the punctured spectrum restricts to
that scheme. -/
private noncomputable def puncturedAffineHullIso (hdepth : 2 ≤ _root_.IsLocalRing.depth
    (ModuleCat.of A A)) (V : Over (puncturedSpectrum A).toScheme) [IsAffineHom V.hom] :
    V ≅ (Over.pullback (puncturedSpectrum A).ι).obj
      ((algSpec (.of A)).obj ((algΓ (.of A)).obj ((Over.map (puncturedSpectrum A).ι).obj V))) := by
  let h := (isPullback_puncturedSpectrum_toSpecΓ A hdepth V.hom).flip
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- Let `A` be a Noetherian local ring of depth at least two, with punctured spectrum `U`, and
let `V` be affine over `U`. If `Spec B` and its restriction to `U` have the same global
functions, then `U`-morphisms from that restriction to `V` correspond to `A`-algebra maps
`Γ(V, 𝒪_V) → B`. The `A`-algebra structure on `Γ(V, 𝒪_V)` comes from `V → U → Spec A`. -/
noncomputable def puncturedHomEquivAlgHom (hdepth : 2 ≤ _root_.IsLocalRing.depth
    (ModuleCat.of A A)) (V : Over (puncturedSpectrum A).toScheme) [IsAffineHom V.hom]
    (B : CommAlgCat.{u} (CommRingCat.of A))
    (hB : IsIso (pullback.fst ((algSpec (.of A)).obj (op B)).hom (puncturedSpectrum A).ι).appTop) :
    ((Over.pullback (puncturedSpectrum A).ι).obj ((algSpec (.of A)).obj (op B)) ⟶ V) ≃
      (((algΓ (.of A)).obj ((Over.map (puncturedSpectrum A).ι).obj V)).unop →ₐ[A] B) :=
  have e := puncturedAffineHullIso hdepth V
  have : IsAffine ((algSpec (.of A)).obj
      ((algΓ (.of A)).obj ((Over.map (puncturedSpectrum A).ι).obj V))).left :=
    inferInstanceAs (IsAffine (Spec Γ(V.left, ⊤)))
  (Iso.homCongr (.refl _) e).trans <|
    (Equiv.ofBijective _ (TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop
      (puncturedSpectrum A).ι hB)).symm.trans <| algSpecHomEquivAlgHom _ B

/-- Precomposing a map from a punctured affine scheme by a morphism of test schemes
postcomposes its corresponding algebra map. -/
theorem puncturedHomEquivAlgHom_map_comp (hdepth : 2 ≤ _root_.IsLocalRing.depth
    (ModuleCat.of A A)) (V : Over (puncturedSpectrum A).toScheme) [IsAffineHom V.hom]
    {B B' : CommAlgCat.{u} (CommRingCat.of A)} (b : B ⟶ B')
    (hB : IsIso (pullback.fst ((algSpec (.of A)).obj (op B)).hom (puncturedSpectrum A).ι).appTop)
    (hB' : IsIso (pullback.fst ((algSpec (.of A)).obj (op B')).hom (puncturedSpectrum A).ι).appTop)
    (f : (Over.pullback (puncturedSpectrum A).ι).obj ((algSpec (.of A)).obj (op B)) ⟶ V) :
    puncturedHomEquivAlgHom hdepth V B' hB'
      ((Over.pullback (puncturedSpectrum A).ι).map ((algSpec (.of A)).map b.op) ≫ f) =
        b.hom.comp (puncturedHomEquivAlgHom hdepth V B hB f) := by
  obtain ⟨φ, rfl⟩ := (puncturedHomEquivAlgHom hdepth V B hB).symm.surjective f
  rw [Equiv.apply_symm_apply, ← Equiv.eq_symm_apply]
  simp only [puncturedHomEquivAlgHom, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.symm_symm, Equiv.ofBijective_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.symm_inv, Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  rw [algSpecHomEquivAlgHom_symm_apply, algSpecHomEquivAlgHom_symm_apply,
    CommAlgCat.ofHom_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]
  simp only [CommAlgCat.ofHom_hom]

section BaseChange

variable {A' B : Type u} [CommRing A'] [IsLocalRing A'] [IsNoetherianRing A']
  [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]

omit [IsNoetherianRing A] in
/-- Let `A → A'` be a map of local rings for which the only prime over the closed point is the
closed point of `Spec A'`. If `A'` is Noetherian of depth at least two and `B` is flat over `A'`,
then `B` is recovered from the functions on `Spec B` over the punctured spectrum of `A`. Here
`B` need not be flat over `A`; in particular `A'` may be a quotient of `A`. -/
theorem isIso_appTop_pullback_fst_puncturedSpectrum_of_flat [Module.Flat A' B]
    (h : ((_root_.IsLocalRing.maximalIdeal A).map (algebraMap A A')).radical =
      _root_.IsLocalRing.maximalIdeal A') (hdepth : 2 ≤ _root_.IsLocalRing.depth
        (ModuleCat.of A' A')) :
    IsIso (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (puncturedSpectrum A).ι).appTop := by
  let U := puncturedSpectrum A
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g' := Spec.map (CommRingCat.ofHom (algebraMap A' B))
  have hW : g ⁻¹ᵁ U = g' ⁻¹ᵁ puncturedSpectrum A' := by
    have hg : g = g' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun r : A →+* B ↦ Spec.map (CommRingCat.ofHom r))
        (IsScalarTower.algebraMap_eq A A' B)
    rw [hg, Scheme.Hom.comp_preimage, preimage_puncturedSpectrum h]
  have : IsIso (g ⁻¹ᵁ U).ι.appTop := by
    rw [Scheme.Opens.ι_appTop]
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat hdepth _ ?_
    intro p hp
    rw [Scheme.Opens.ι_image_top, hW]
    exact (mem_preimage_puncturedSpectrum_iff A' p).mpr hp
  have he : (pullbackRestrictIsoRestrict g U).hom ≫ (g ⁻¹ᵁ U).ι = pullback.fst g U.ι :=
    pullbackRestrictIsoRestrict_hom_ι g U
  have : IsIso (pullbackRestrictIsoRestrict g U).hom.appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map (pullbackRestrictIsoRestrict g U).hom.op))
  rw [← he, Scheme.Hom.comp_appTop]
  infer_instance

end BaseChange

/-- Let `A` be a Noetherian local ring of depth at least three, `a` a nonzerodivisor,
and `B` a flat `A`-algebra. On every positive-order thickening `B/aⁿB`, restriction to the
preimage of the punctured spectrum of `A` preserves the ring of global functions. -/
theorem isIso_appTop_pullback_fst_puncturedSpectrum_quotient_pow {B : Type u}
    [CommRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : 3 ≤ _root_.IsLocalRing.depth (ModuleCat.of A A))
    {a : A} (ha' : IsSMulRegular A a) (n : ℕ) :
    IsIso (pullback.fst (Spec.map (CommRingCat.ofHom
      (algebraMap A (B ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B)))))
      (puncturedSpectrum A).ι).appTop := by
  let I : Ideal A := Ideal.span {a ^ (n + 1)}
  by_cases ha : a ∈ _root_.IsLocalRing.maximalIdeal A
  swap
  · -- A unit defines the empty thickening.
    have htop : I = ⊤ := Ideal.span_singleton_eq_top.mpr
      ((_root_.IsLocalRing.notMem_maximalIdeal.mp ha).pow _)
    have : Subsingleton (B ⧸ I.map (algebraMap A B)) :=
      Ideal.Quotient.subsingleton_iff.mpr (htop ▸ Ideal.map_top _)
    let j := (pullback.fst (Spec.map (CommRingCat.ofHom
      (algebraMap A (B ⧸ I.map (algebraMap A B))))) (puncturedSpectrum A).ι).appTop
    have : Subsingleton Γ(Spec (.of (B ⧸ I.map (algebraMap A B))), ⊤) :=
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.toRingHom.codomain_trivial
    have := j.hom.codomain_trivial
    exact (ConcreteCategory.isIso_iff_bijective j).mpr (Function.bijective_of_subsingleton' _)
  have hx : a ^ (n + 1) ∈ _root_.IsLocalRing.maximalIdeal A :=
    Ideal.pow_mem_of_mem _ ha _ (Nat.succ_pos n)
  have hI : I ≤ _root_.IsLocalRing.maximalIdeal A := (Ideal.span_singleton_le_iff_mem _).mpr hx
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (_root_.IsLocalRing.maximalIdeal.isMaximal A).ne_top hI)
  have hs : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  have : IsLocalRing (A ⧸ I) := _root_.IsLocalRing.of_surjective' _ hs
  have : IsNoetherianRing (A ⧸ I) := isNoetherianRing_of_surjective A _ _ hs
  have : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  refine isIso_appTop_pullback_fst_puncturedSpectrum_of_flat
    (A' := A ⧸ I) (B := B ⧸ I.map (algebraMap A B)) (radical_map_maximalIdeal_of_surjective hs) ?_
  have hker : LinearMap.ker I.mkQ = a ^ (n + 1) • (⊤ : Submodule A A) := by
    rw [Submodule.ker_mkQ, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  have hdepth' := _root_.IsLocalRing.depth_eq_add_one_of_surjective hx (ha'.pow (n + 1))
    I.mkQ I.mkQ_surjective hker
  rw [_root_.IsLocalRing.depth_eq_depth_of_surjective (M := A ⧸ I) hs] at hdepth'
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp (hdepth.trans_eq hdepth')

end TauCeti.IsLocalRing
