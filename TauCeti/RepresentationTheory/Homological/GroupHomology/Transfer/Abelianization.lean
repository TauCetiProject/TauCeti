/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.Transfer
public import TauCeti.RepresentationTheory.Homological.Augmentation
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Delta
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# The transfer on first homology is the Verlagerung

Let `S` be a subgroup of a finite group `G` and `A` a trivial representation over a commutative
ring `k`. With trivial coefficients, first group homology is the abelianization tensored with the
coefficients, `H₁(G, A) ≃ Gᵃᵇ ⊗ A` (Mathlib's `groupHomology.H1AddEquivOfIsTrivial`). This file
proves that, under these identifications, the homological transfer `H₁(G, A) ⟶ H₁(S, A)` of
`TauCeti.groupHomology.transfer` is the group-theoretic transfer (Verlagerung)
`Gᵃᵇ → Sᵃᵇ` of Mathlib's `MonoidHom.transfer`, tensored with `A`.

By naturality of the transfer in the coefficients it suffices to treat `A = k`. That case is
proved by dimension shifting along the augmentation sequence
`0 ⟶ I_G ⟶ k[G] ⟶ k ⟶ 0`. The transfer commutes with its connecting maps
(`TauCeti.groupHomology.δ_comp_transfer`), the connecting map `H₁(S, k) ⟶ H₀(S, I_G)` is injective
because `H₁(S, k[G]) = 0`, and in degree zero the transfer is the relative transfer
`⟦m⟧ ↦ ⟦∑_{q ∈ G ⧸ S} q⁻¹ • m⟧` (`TauCeti.groupHomology.transfer_zero_H0π`), which on the class
`[g⁻¹] - [1]` of `g ∈ G` is computed coset by coset.

## Main results

* `TauCeti.groupHomology.isZero_groupHomology_res_leftRegular`: for a finite subgroup `S ≤ G`,
  `Hₙ(S, k[G]) = 0` for `n > 0`.
* `TauCeti.groupHomology.transfer_mkH1OfIsTrivial`: the transfer sends the class of `g ⊗ a` to the
  class of `V(g) ⊗ a`, where `V : Gᵃᵇ → Sᵃᵇ` is the Verlagerung.
* `TauCeti.groupHomology.H1AddEquivOfIsTrivial_transfer`: the same statement for every class,
  through `H₁(G, k) ≃ Gᵃᵇ ⊗ k`.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* J.-P. Serre, *Local Fields*, Chapter VII, §8.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep Finsupp

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G]

section Augmentation

/-! ### Elements of the augmentation ideal

The augmentation ideal is a categorical kernel, so its elements are named through their images in
`k[G]`: `augElt a h` is the element mapping to `[h] a - [1] a`. -/

variable (k G) in
/-- The augmentation sequence, with its maps named. -/
private theorem shortExact_aug :
    (ShortComplex.mk (augmentationι k G) (augmentation k G)
      (augmentationι_comp_augmentation k G)).ShortExact :=
  augmentationSES_def k G ▸ augmentationSES_shortExact k G

variable (k G) in
private theorem exact_aug :
    Function.Exact (augmentationι k G).hom (augmentation k G).hom := by
  have h := (shortExact_aug k G).exact.map (forget₂ (Rep k G) (ModuleCat k))
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h

private theorem augmentation_single_sub (a : k) (h : G) :
    (augmentation k G).hom (MonoidAlgebra.single h a - MonoidAlgebra.single 1 a) = 0 := by
  rw [map_sub]
  simp

/-- An element of the augmentation ideal mapping to `[h] a - [1] a`. -/
private def augElt (a : k) (h : G) : augmentationIdeal k G :=
  Classical.choose <| (exact_aug k G _).1 (augmentation_single_sub a h)

private theorem augElt_spec (a : k) (h : G) :
    (augmentationι k G).hom (augElt a h) = MonoidAlgebra.single h a - MonoidAlgebra.single 1 a :=
  Classical.choose_spec <| (exact_aug k G _).1 (augmentation_single_sub a h)

private theorem ι_injective : Function.Injective (augmentationι k G).hom :=
  (Rep.mono_iff_injective _).1 inferInstance

/-- `G` acts on the elements `augElt a y` through the left regular action on `y`. -/
private theorem ρ_augElt (a : k) (x y : G) :
    (augmentationIdeal k G).ρ x (augElt a y) = augElt a (x * y) - augElt a x := by
  apply ι_injective
  rw [hom_comm_apply, map_sub, augElt_spec, augElt_spec, augElt_spec, map_sub]
  simp

private theorem augElt_one (a : k) : augElt a (1 : G) = 0 := by
  apply ι_injective
  rw [augElt_spec, sub_self, map_zero]

end Augmentation

section Transfer

variable (S : Subgroup G)

/-- The class of `augElt a y` in `H₀(S, I_G)`. -/
private abbrev θ (a : k) (y : G) : H0 (res S.subtype (augmentationIdeal k G)) :=
  H0π (res S.subtype (augmentationIdeal k G)) (augElt a y)

variable {S} in
/-- `θ` is additive in a left factor from `S`, because `S` acts trivially on `H₀(S, I_G)`. -/
private theorem θ_mul (a : k) {s : G} (hs : s ∈ S) (y : G) :
    θ S a (s * y) = θ S a s + θ S a y := by
  have h := ρ_augElt a s y
  rw [eq_sub_iff_add_eq] at h
  have h2 : H0π (res S.subtype (augmentationIdeal k G))
      ((augmentationIdeal k G).ρ s (augElt a y)) =
        H0π (res S.subtype (augmentationIdeal k G)) (augElt a y) :=
    (H0π_eq_iff _).2 (Representation.Coinvariants.sub_mem_ker (ρ := (res S.subtype
      (augmentationIdeal k G)).ρ) ⟨s, hs⟩ _)
  rw [θ, θ, θ, ← h, map_add, h2, add_comm]

/-- `s ↦ [augElt a s]` as a homomorphism out of the abelianization of `S`. -/
private def ψ (a : k) :
    Abelianization S →* Multiplicative (H0 (res S.subtype (augmentationIdeal k G))) :=
  Abelianization.lift
    { toFun s := Multiplicative.ofAdd (θ S a s)
      map_one' := by simp [θ, augElt_one]
      map_mul' s t := by
        simp only [Subgroup.coe_mul, θ_mul a s.2, ofAdd_add] }

private theorem ψ_of (a : k) (s : S) : ψ S a (Abelianization.of s) = .ofAdd (θ S a s) := by
  simp [ψ]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The relative transfer of `augElt a h` is the transfer of `h` into `Sᵃᵇ`, read through `ψ`. -/
private theorem H0π_relTransfer_augElt [S.FiniteIndex] (a : k) (h : G) :
    H0π (res S.subtype (augmentationIdeal k G))
        (Representation.relTransfer (augmentationIdeal k G).ρ S (augElt a h)) =
      (ψ S a ((Abelianization.of : S →* Abelianization S).transfer h)).toAdd := by
  rw [MonoidHom.transfer_eq_prod_of_bijective _ (fun q : G ⧸ S ↦ q.out) (by simp) h (h • ·)
    (QuotientGroup.mk_out_smul h), map_prod, toAdd_prod, Representation.relTransfer_apply,
    map_sum]
  simp_rw [ρ_augElt, map_sub]
  rw [Finset.sum_sub_distrib, ← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (G ⧸ S))]
  simp_rw [ψ_of, toAdd_ofAdd]
  rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- `(h q).out⁻¹ h = s q.out⁻¹` with `s = (h q).out⁻¹ h q.out ∈ S`, and `θ` is additive in the
  -- `S`-factor.
  have hs : (h • q).out⁻¹ * (h * q.out) ∈ S := QuotientGroup.eq.mp (QuotientGroup.mk_out_smul h q)
  rw [MulAction.toPerm_apply, ← θ_mul a hs, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

/-- The connecting map `H₁(G, k) ⟶ H₀(G, I_G)` of the augmentation sequence sends the class of
`g ⊗ a` to the class of `[g⁻¹] a - [1] a`. -/
private theorem δ_mkH1OfIsTrivial (g : G) (a : k) :
    δ (shortExact_aug k G) 1 0 rfl
        (mkH1OfIsTrivial (trivial k G k) (Additive.ofMul (Abelianization.of g)) a) =
      H0π (augmentationIdeal k G) (augElt a g⁻¹) := by
  rw [mkH1OfIsTrivial_apply]
  exact δ₀_apply (shortExact_aug k G) _ (single g (MonoidAlgebra.single 1 a))
    (by rw [cycles₁IsoOfIsTrivial_inv_apply]; simp) _ (by rw [augElt_spec, d₁₀_single]; simp)

/-- The connecting map `H₁(S, k) ⟶ H₀(S, I_G)` of the restricted augmentation sequence, on the
class of `x ⊗ a`. -/
private theorem δ_res_mkH1OfIsTrivial (x : Abelianization S) (a : k) :
    δ ((shortExact_res S.subtype).2 (shortExact_aug k G)) 1 0 rfl
        (mkH1OfIsTrivial (res S.subtype (trivial k G k)) (Additive.ofMul x) a) =
      (ψ S a x⁻¹).toAdd := by
  obtain ⟨s, rfl⟩ : ∃ s : S, Abelianization.of s = x := QuotientGroup.mk'_surjective _ x
  rw [mkH1OfIsTrivial_apply, ← map_inv, ψ_of, toAdd_ofAdd]
  exact δ₀_apply ((shortExact_res S.subtype).2 (shortExact_aug k G)) _
    (single s (MonoidAlgebra.single 1 a)) (by rw [cycles₁IsoOfIsTrivial_inv_apply]; simp) _
    (by rw [d₁₀_single]; exact (augElt_spec a _).trans (by simp))

variable (k) in
/-- For a finite subgroup `S` of `G`, the group homology of `S` with coefficients in the
restriction of `k[G]` vanishes in positive degrees. -/
theorem isZero_groupHomology_res_leftRegular [Finite S] (n : ℕ) [NeZero n] :
    IsZero (groupHomology (res S.subtype (leftRegular k G)) n) :=
  have : Fintype S := Fintype.ofFinite S
  (TauCeti.TateCohomology.isZero_res_leftRegular S (-(n + 1))).of_iso
    ((_root_.TateCohomology.isoGroupHomology (-(n + 1)) n rfl).app _).symm

/-- `transfer_mkH1OfIsTrivial` for the coefficients `k` themselves. -/
private theorem transfer_mkH1OfIsTrivial_trivial [Finite G] (x : Additive (Abelianization G))
    (a : k) :
    transfer (trivial k G k) S 1 (mkH1OfIsTrivial (trivial k G k) x a) =
      mkH1OfIsTrivial (res S.subtype (trivial k G k))
        ((Abelianization.lift (Abelianization.of : S →* Abelianization S).transfer).toAdditive x)
        a := by
  obtain ⟨g, rfl⟩ : ∃ g : G, Additive.ofMul (Abelianization.of g) = x :=
    QuotientGroup.mk'_surjective _ x.toMul
  -- The connecting map of the augmentation sequence restricted to `S` is injective on `H₁(S, k)`,
  -- and it carries both sides to the same class of `H₀(S, I_G)`: the left side through the
  -- degree-zero transfer, the right side directly.
  have hXS := (shortExact_res S.subtype).2 (shortExact_aug k G)
  have : Mono (δ hXS 1 0 rfl) :=
    mono_δ_of_isZero hXS 0 (isZero_groupHomology_res_leftRegular k S 1)
  apply (ModuleCat.mono_iff_injective _).1 this
  rw [MonoidHom.toAdditive_apply_apply, toMul_ofMul, Abelianization.lift_apply_of,
    δ_res_mkH1OfIsTrivial, ← map_inv, ← H0π_relTransfer_augElt, ← transfer_zero_H0π,
    ← δ_mkH1OfIsTrivial, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    δ_comp_transfer S (shortExact_aug k G) 1 0 rfl]

/-- **The transfer on `H₁` with trivial coefficients is the Verlagerung.** For a subgroup `S` of a
finite group `G` and trivial coefficients `A`, the transfer `H₁(G, A) ⟶ H₁(S, A)` sends the class
of `x ⊗ a` to the class of `V x ⊗ a`, where `V : Gᵃᵇ → Sᵃᵇ` is the group-theoretic transfer
`MonoidHom.transfer` of `Abelianization.of : S →* Sᵃᵇ`, descended to `Gᵃᵇ`. -/
@[simp]
theorem transfer_mkH1OfIsTrivial [Finite G] (A : Rep k G) [A.IsTrivial]
    (x : Additive (Abelianization G)) (a : A) :
    transfer A S 1 (mkH1OfIsTrivial A x a) =
      mkH1OfIsTrivial (res S.subtype A)
        ((Abelianization.lift (Abelianization.of : S →* Abelianization S).transfer).toAdditive x)
        a := by
  -- `a` is the image of `1` under the morphism `k ⟶ A`, `1 ↦ a`, and the transfer is natural in
  -- the coefficients.
  let φ : trivial k G k ⟶ A := Rep.ofHom <| (LinearMap.toSpanSingleton k A a)
    |>.intertwiningMap_of_isIntertwiningMap (Representation.trivial k G k) A.ρ fun g v ↦ by
      simp [Representation.isTrivial_apply]
  have hφ : φ.hom 1 = a := by simp [φ]
  have h := map_mkH1OfIsTrivial (B := A) (MonoidHom.id G) φ x 1
  rw [Abelianization.map_id, MonoidHom.toAdditive_id, AddMonoidHom.id_apply, hφ] at h
  rw [← h, map_comp_transfer_apply, transfer_mkH1OfIsTrivial_trivial, map_mkH1OfIsTrivial,
    Abelianization.map_id, MonoidHom.toAdditive_id, AddMonoidHom.id_apply]
  rw [Rep.resMap_hom_apply, hφ]

/-- **The transfer on `H₁` with trivial coefficients is the Verlagerung**, read through the
identifications `H₁(G, A) ≃ Gᵃᵇ ⊗ A` and `H₁(S, A) ≃ Sᵃᵇ ⊗ A`: the transfer becomes `V ⊗ A`, for
`V : Gᵃᵇ → Sᵃᵇ` the group-theoretic transfer. -/
@[simp]
theorem H1AddEquivOfIsTrivial_transfer [Finite G] (A : Rep k G) [A.IsTrivial] (x : H1 A) :
    H1AddEquivOfIsTrivial (res S.subtype A) (transfer A S 1 x) =
      LinearMap.rTensor A (AddMonoidHom.toIntLinearMap
        (Abelianization.lift (Abelianization.of : S →* Abelianization S).transfer).toAdditive)
        (H1AddEquivOfIsTrivial A x) := by
  obtain ⟨t, rfl⟩ := (H1AddEquivOfIsTrivial A).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul y a =>
    obtain ⟨g, rfl⟩ : ∃ g : G, Additive.ofMul (Abelianization.of g) = y :=
      QuotientGroup.mk'_surjective _ y.toMul
    obtain ⟨s, hs⟩ : ∃ s : S, Abelianization.of s =
        (Abelianization.of : S →* Abelianization S).transfer g :=
      QuotientGroup.mk'_surjective _ _
    rw [H1AddEquivOfIsTrivial_symm_tmul, ← mkH1OfIsTrivial_apply, transfer_mkH1OfIsTrivial]
    simpa [← hs] using H1AddEquivOfIsTrivial_single (res S.subtype A) s a
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

end Transfer

end TauCeti.groupHomology
