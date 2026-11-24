/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Reciprocity
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
import TauCeti.Algebra.AddCircle
import TauCeti.Algebra.Group.Pi.Pairing
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Finiteness
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree

/-!
# Weak global duality for the Selmer groups of an isogeny and its dual

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over a number field `K`, with dual `φ̂`, and
let `S` be a finite set of finite places of `K`. Write `H¹_φ(K_v) ⊆ H¹(K_v, E₁[φ])` for the local
condition of `Sel_φ` at `v`, the kernel of `H¹(K_v, E₁[φ]) → H¹(K_v, E₁)`. Two Selmer groups
compare the conditions at `S`:

* the `φ`-Selmer group relaxed at `S`, `Sel_φ^S ⊇ Sel_φ`, cut out by the local conditions at the
  places outside `S` only, finite and infinite;
* the `φ̂`-Selmer classes that vanish at the places of `S`, a subgroup of `Sel_φ̂`.

This file proves the inequality

`[Sel_φ^S : Sel_φ] · [Sel_φ̂ : Sel_φ̂ ∩ ker(loc_S)] ≤ ∏_{v ∈ S} [H¹(K_v, E₁[φ]) : H¹_φ(K_v)]`

(`TauCeti.Isogeny.relIndex_selmerGroup_mul_relIndex_ker_le_prod_index`), where
`loc_S : H¹(K, E₂[φ̂]) → ∏_{v ∈ S} H¹(K_v, E₂[φ̂])` is the localisation at `S`. The first factor is
the order of the image of `Sel_φ^S` in `∏_{v ∈ S} H¹(K_v, E₁[φ]) / H¹_φ(K_v)`, the second the
order of the image of `Sel_φ̂` in `∏_{v ∈ S} H¹_φ̂(K_v)`. Under the sum of the local Tate pairings
these two images are orthogonal: global reciprocity for the isogeny Weil cup product
(`TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero`) kills the pairing of the
images of global classes, and the local conditions of `φ` and `φ̂` are orthogonal at every place.
As each local pairing identifies `H¹(K_v, E₁[φ])` with the characters of `H¹(K_v, E₂[φ̂])`,
orthogonality bounds the product of the orders of the images
(`AddMonoidHom.natCard_mul_natCard_le_of_forall_eq_zero_zmod`).

This is the orthogonality half of global duality for the Selmer groups of `φ` and `φ̂`. Poitou–Tate
duality shows that the two images are exact annihilators of one another, so that equality holds;
that equality is the step comparing the local conditions in the proof of Cassels' formula for the
ratio `#Sel_φ / #Sel_φ̂`. The finiteness of the local cohomology groups at the places of `S`
comes from viewing each completion as a finite extension of `ℚ_p`
(`IsDedekindDomain.HeightOneSpectrum.finitePadicExtension`).

## Main definitions

* `TauCeti.Isogeny.kerResPi` and `TauCeti.Isogeny.dualKerResPi`: localisation of
  `H¹(K, E₁[φ])` and of `H¹(K, E₂[φ̂])` at the places of `S`.

## Main results

* `TauCeti.Isogeny.relIndex_selmerGroup_mul_relIndex_ker_le_prod_index`: the inequality above.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §4 (Theorem 4.10) and §7.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom
open IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
  (S : Finset (HeightOneSpectrum (𝓞 K)))

section Localization

variable (τ : ∀ v : HeightOneSpectrum (𝓞 K),
  SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- **Localisation of `H¹(K, E₁[φ])` at the finite places of `S`**: the restrictions
`φ.kerRes (τ v)` to the completions `K_v`, `v ∈ S`. -/
def kerResPi :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      ∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.val.adicCompletion K))).KerCoeff :=
  AddMonoidHom.pi fun v ↦ φ.kerRes (τ v.val)

@[simp]
theorem kerResPi_apply (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) (v : S) :
    φ.kerResPi S τ c v = φ.kerRes (τ v.val) c :=
  (rfl)

/-- A class lies in the kernel of `kerResPi` exactly when it restricts to zero at every place
of `S`. -/
theorem mem_ker_kerResPi_iff {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ (φ.kerResPi S τ).ker ↔ ∀ v ∈ S, φ.kerRes (τ v) c = 0 := by
  simp [funext_iff]

/-- **Localisation of `H¹(K, E₂[φ̂])` at the finite places of `S`**: the restrictions
`φ.dualKerRes (τ v)` into the kernels of the duals of the base changes of `φ`, on which the local
Tate pairings of `φ` are defined. -/
def dualKerResPi :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff →+
      ∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.val.adicCompletion K)).dual).KerCoeff :=
  AddMonoidHom.pi fun v ↦ φ.dualKerRes (τ v.val)

@[simp]
theorem dualKerResPi_apply (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff)
    (v : S) : φ.dualKerResPi S τ c v = φ.dualKerRes (τ v.val) c :=
  (rfl)

/-- A class lies in the kernel of `dualKerResPi` exactly when it restricts to zero at every
place of `S`. -/
theorem mem_ker_dualKerResPi_iff {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} :
    c ∈ (φ.dualKerResPi S τ).ker ↔ ∀ v ∈ S, φ.dualKerRes (τ v) c = 0 := by
  simp [funext_iff]

end Localization

/-! ### The sum of the local Tate pairings over `S` -/

/-- The local Tate pairing of the base change of `φ` to `K_v`, with values transported from
`ℤ / deg (φ_{K_v})` to `ℤ / deg φ`. -/
private def localPairing (v : HeightOneSpectrum (𝓞 K)) :
    H1 (AbsoluteGaloisGroup (v.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff →+
      H1 (AbsoluteGaloisGroup (v.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.adicCompletion K)).dual).KerCoeff →+ ZMod φ.degree :=
  (AddMonoidHom.compHom (ZMod.ringEquivCongr (degree_baseChange φ)).toAddMonoidHom).comp
    ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
      (isUnit_natCast_of_ne_zero (φ.baseChange (v.adicCompletion K)).degree_ne_zero))

private theorem localPairing_apply (v : HeightOneSpectrum (𝓞 K)) (a b) :
    localPairing φ v a b = ZMod.ringEquivCongr (degree_baseChange φ)
      ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (isUnit_natCast_of_ne_zero (φ.baseChange (v.adicCompletion K)).degree_ne_zero) a b) :=
  (rfl)

private theorem injective_localPairing (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (localPairing φ v) := fun a b h ↦
  ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing_bijective _).injective <|
    AddMonoidHom.ext fun y ↦ (ZMod.ringEquivCongr (degree_baseChange φ)).injective <| by
      simpa only [localPairing_apply] using DFunLike.congr_fun h y

/-- The local conditions of `φ` and `φ̂` are orthogonal under `localPairing`. -/
private theorem localPairing_eq_zero_of_mem_ker (v : HeightOneSpectrum (𝓞 K))
    {a : H1 (AbsoluteGaloisGroup (v.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup (v.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.adicCompletion K)).dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K)).dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    localPairing φ v a b = 0 := by
  rw [localPairing_apply, localTateKerWeilPairing_apply,
    (φ.baseChange (v.adicCompletion K)).kerH1WeilPairing_eq_zero_of_mem_ker _ ha hb, map_zero,
    map_zero, map_zero]

/-! ### Selmer groups relaxed at `S` -/

section Selmer

variable (τ : ∀ v : GlobalNumberFields.Place K,
  SeparableClosure K →ₐ[K] SeparableClosure v.Completion)

/-- The local condition of `φ` at a finite place `v`: the kernel of
`H¹(K_v, E₁[φ]) → H¹(K_v, E₁)`. -/
private def localCondition (v : HeightOneSpectrum (𝓞 K)) :
    AddSubgroup (H1 (AbsoluteGaloisGroup (v.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff) :=
  (explicitCoeff1 (AbsoluteGaloisGroup (v.adicCompletion K)) _
    (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
    continuous_of_discreteTopology).ker

/-- The product over `S` of the local conditions of `φ`. -/
private def localConditionPi :
    AddSubgroup (∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.val.adicCompletion K))).KerCoeff) :=
  AddSubgroup.pi Set.univ fun v ↦ localCondition φ v.val

/-- At a place `v ∈ S`, the localisation of a class satisfies the local condition of `φ` exactly
when its image in `H¹(K, E₁)` restricts to zero at `v`. -/
private theorem kerResPi_mem_localCondition_iff
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ S) :
    φ.kerResPi S (fun v ↦ τ (.inl v)) c ⟨v, hv⟩ ∈ localCondition φ v ↔
      W₁.pointRes (τ (.inl v))
        (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology c) = 0 := by
  rw [pointRes_kerCoeffIncl]
  -- The left side is stated over the adic completion, the right side over the completion
  -- indexed by the place `Sum.inl v`; the two agree definitionally.
  exact Iff.rfl

/-- `Sel_φ` consists of the classes of the Selmer group relaxed at `S` that satisfy the local
conditions at the places of `S`. -/
private theorem selmerGroup_eq_inf_comap :
    φ.selmerGroup τ =
      (φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦ τ w) ⊓
        (localConditionPi φ S).comap (φ.kerResPi S fun v ↦ τ (.inl v)) := by
  ext c
  simp only [AddSubgroup.mem_inf, mem_selmerGroup_iff, mem_shafarevichTateGroup_iff,
    AddSubgroup.mem_comap, localConditionPi, AddSubgroup.mem_pi, Set.mem_univ, forall_const]
  constructor
  · exact fun h ↦ ⟨fun w ↦ h w, fun v ↦
      (φ.kerResPi_mem_localCondition_iff S τ c v.property).2 (h (.inl v.val))⟩
  · intro hc w
    by_cases hw : ∃ v ∈ S, w = .inl v
    · obtain ⟨v, hv, rfl⟩ := hw
      exact (φ.kerResPi_mem_localCondition_iff S τ c hv).1 (hc.2 ⟨v, hv⟩)
    · push Not at hw
      exact hc.1 ⟨w, hw⟩

/-- The embedding of separable closures at a finite place `v`, from a family indexed by all
places, read over the adic completion `K_v`. It is `τ (.inl v)`, retyped so that it can be passed
to global reciprocity. -/
private def finEmb (v : HeightOneSpectrum (𝓞 K)) :
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K) :=
  τ (.inl v)

/-- The embedding of separable closures at an infinite place `w`, read over `K_w`. -/
private def infEmb (w : InfinitePlace K) :
    SeparableClosure K →ₐ[K] SeparableClosure w.Completion :=
  τ (.inr w)

private theorem pointRes_finEmb {W : WeierstrassCurve K} (v : HeightOneSpectrum (𝓞 K))
    (x : H1 (AbsoluteGaloisGroup K) W.PointCoeff) :
    W.pointRes (finEmb τ v) x = W.pointRes (τ (.inl v)) x :=
  (rfl)

private theorem pointRes_infEmb {W : WeierstrassCurve K} (w : InfinitePlace K)
    (x : H1 (AbsoluteGaloisGroup K) W.PointCoeff) :
    W.pointRes (infEmb τ w) x = W.pointRes (τ (.inr w)) x :=
  (rfl)

/-- **Global orthogonality.** A class of the `φ`-Selmer group relaxed at `S` and a class of
`Sel_φ̂` have local pairings at the places of `S` summing to zero. -/
private theorem sum_localPairing_eq_zero {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (ha : a ∈ φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦ τ w)
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} (hb : b ∈ φ.dual.selmerGroup τ) :
    AddMonoidHom.piPairing (fun v : S ↦ localPairing φ v.val)
      (φ.kerResPi S (fun v ↦ τ (.inl v)) a) (φ.dualKerResPi S (fun v ↦ τ (.inl v)) b) = 0 := by
  have : NeZero φ.degree := ⟨φ.degree_ne_zero⟩
  rw [mem_selmerGroup_iff, mem_shafarevichTateGroup_iff] at ha hb
  apply ZMod.toRatAddCircle_injective φ.degree
  rw [AddMonoidHom.piPairing_apply, map_sum, map_zero]
  simp only [kerResPi_apply, dualKerResPi_apply, localPairing_apply,
    ZMod.toRatAddCircle_ringEquivCongr]
  -- Reciprocity takes the family `finEmb τ`, which unfolds to the family `fun v ↦ τ (.inl v)` of
  -- the statement.
  refine (Finset.sum_coe_sort S _).trans <|
    φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero a b (finEmb τ) (infEmb τ) S
      (fun v hv ↦ ?_) (fun v _ ↦ ?_) (fun w ↦ ?_) (fun w ↦ ?_)
  · rw [pointRes_finEmb]
    exact ha ⟨.inl v, fun v' hv' h ↦ hv (Sum.inl_injective h ▸ hv')⟩
  · rw [pointRes_finEmb]
    exact hb (.inl v)
  · rw [pointRes_infEmb]
    exact ha ⟨.inr w, fun _ _ h ↦ Sum.inr_ne_inl h⟩
  · rw [pointRes_infEmb]
    exact hb (.inr w)

/-- The images of the relaxed Selmer group of `φ`, enlarged by the local conditions, and of
`Sel_φ̂` are orthogonal under the sum of the local pairings over `S`. -/
private theorem piPairing_eq_zero
    {x : ∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.val.adicCompletion K))).KerCoeff}
    (hx : x ∈ (φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦
      τ w).map (φ.kerResPi S fun v ↦ τ (.inl v)) ⊔ localConditionPi φ S)
    {y : ∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.val.adicCompletion K)).dual).KerCoeff}
    (hy : y ∈ (φ.dual.selmerGroup τ).map (φ.dualKerResPi S fun v ↦ τ (.inl v))) :
    AddMonoidHom.piPairing (fun v : S ↦ localPairing φ v.val) x y = 0 := by
  obtain ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [_root_.map_add, AddMonoidHom.add_apply, φ.sum_localPairing_eq_zero S τ ha hb, zero_add,
    AddMonoidHom.piPairing_apply]
  refine Finset.sum_eq_zero fun v _ ↦ localPairing_eq_zero_of_mem_ker φ v.val
    (hz v (Set.mem_univ v)) ?_
  rw [SetLike.mem_coe, mem_selmerGroup_iff, mem_shafarevichTateGroup_iff] at hb
  rw [AddMonoidHom.mem_ker, dualKerResPi_apply, ← pointRes_dualKerCoeffIncl]
  exact hb (.inl v.val)

end Selmer

/-- The orders of the products over `S` of the local cohomology groups: that of
`H¹(K_v, E₂[φ̂])` is the order of the product of the local conditions of `φ` times the product of
their indices. -/
private theorem natCard_pi_H1_kerCoeff_dual :
    Nat.card (∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.val.adicCompletion K)).dual).KerCoeff) =
      Nat.card (localConditionPi φ S) * ∏ v ∈ S, (localCondition φ v).index := by
  have hC : Nat.card (localConditionPi φ S) = ∏ v ∈ S, Nat.card (localCondition φ v) := by
    rw [← Finset.prod_coe_sort S, ← Nat.card_pi]
    exact Nat.card_congr ((Equiv.subtypeEquivRight fun x ↦ by
      simp [localConditionPi, AddSubgroup.mem_pi]).trans Equiv.subtypePiEquivPi)
  rw [hC, ← Finset.prod_mul_distrib, Nat.card_pi, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [(φ.baseChange (v.val.adicCompletion K)).natCard_H1_kerCoeff_dual
    (isUnit_natCast_of_ne_zero (φ.baseChange (v.val.adicCompletion K)).degree_ne_zero),
    AddSubgroup.card_mul_index]

/-- The relative index of `Sel_φ` in the Selmer group relaxed at `S`, times the order of the
product of the local conditions, is the order of the image of the relaxed group in the product of
the local cohomology groups, enlarged by the local conditions. -/
private theorem relIndex_selmerGroup_mul_natCard_localConditionPi
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    (φ.selmerGroup τ).relIndex
        (φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦ τ w) *
      Nat.card (localConditionPi φ S) =
    Nat.card ((φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦
      τ w).map (φ.kerResPi S fun v ↦ τ (.inl v)) ⊔ localConditionPi φ S :) := by
  rw [φ.selmerGroup_eq_inf_comap S τ, AddSubgroup.inf_relIndex_left, AddSubgroup.relIndex_comap,
    ← AddSubgroup.relIndex_sup_right]
  have h := AddSubgroup.relIndex_mul_card (localConditionPi φ S)
    ((φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦
      τ w).map (φ.kerResPi S fun v ↦ τ (.inl v)) ⊔ localConditionPi φ S)
  rwa [inf_of_le_left le_sup_right] at h

/-- **Weak global duality for the Selmer groups of an isogeny and its dual.** Let `φ : E₁ → E₂`
be an isogeny of elliptic curves over a number field `K` and `S` a finite set of finite places of
`K`. The index of `Sel_φ` in the `φ`-Selmer group relaxed at `S`, times the index in `Sel_φ̂` of
the classes vanishing at every place of `S`, is at most the product over `v ∈ S` of the indices
of the local conditions `H¹_φ(K_v) ⊆ H¹(K_v, E₁[φ])`:

`[Sel_φ^S : Sel_φ] · [Sel_φ̂ : Sel_φ̂ ∩ ker(loc_S)] ≤ ∏_{v ∈ S} [H¹(K_v, E₁[φ]) : H¹_φ(K_v)]`.

The two factors on the left are the orders of the images of `Sel_φ^S` and of `Sel_φ̂` in the local
terms at `S`, which global reciprocity makes orthogonal under the perfect local Tate pairings.
Equality is the content of Poitou–Tate duality. -/
theorem relIndex_selmerGroup_mul_relIndex_ker_le_prod_index
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    (φ.selmerGroup τ).relIndex
        (φ.selmerGroup fun w : {w : GlobalNumberFields.Place K // ∀ v ∈ S, w ≠ .inl v} ↦ τ w) *
      (φ.dualKerResPi S fun v ↦ τ (.inl v)).ker.relIndex (φ.dual.selmerGroup τ) ≤
    ∏ v ∈ S, (explicitCoeff1 (AbsoluteGaloisGroup (v.adicCompletion K)) _
      (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
      continuous_of_discreteTopology).ker.index := by
  have hN (y : ∀ v : S, H1 (AbsoluteGaloisGroup (v.val.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.val.adicCompletion K)).dual).KerCoeff) :
      φ.degree • y = 0 := funext fun v ↦ by
    refine nsmul_H1_eq_zero (G := AbsoluteGaloisGroup (v.val.adicCompletion K)) (fun Q ↦ ?_) _
    have h := (φ.baseChange (v.val.adicCompletion K)).dual.degree_nsmul_kerCoeff_eq_zero Q
    rwa [degree_dual, degree_baseChange] at h
  have : NeZero φ.degree := ⟨φ.degree_ne_zero⟩
  have := fun v : S ↦ finite_H1_kerCoeff_adicCompletion v.val _
    (ofIsogeny_ne_zero (φ.baseChange (v.val.adicCompletion K)).dual)
  have hle := AddMonoidHom.natCard_mul_natCard_le_of_forall_eq_zero_zmod _
    (AddMonoidHom.injective_piPairing _ fun v : S ↦ injective_localPairing φ v.val) hN
    (fun x hx y hy ↦ φ.piPairing_eq_zero S τ hx hy)
  rw [← φ.relIndex_selmerGroup_mul_natCard_localConditionPi S τ,
    ← AddSubgroup.relIndex_ker, natCard_pi_H1_kerCoeff_dual] at hle
  have : Finite (localConditionPi φ S) := by
    have := fun v : S ↦ finite_H1_kerCoeff_adicCompletion v.val _
      (ofIsogeny_ne_zero (φ.baseChange (v.val.adicCompletion K)))
    infer_instance
  rw [mul_right_comm, mul_comm _ (∏ v ∈ S, _)] at hle
  exact Nat.le_of_mul_le_mul_right hle (Nat.card_pos_iff.2 ⟨⟨0⟩, ‹_›⟩)

end TauCeti.Isogeny
