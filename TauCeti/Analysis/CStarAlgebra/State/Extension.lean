/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Extension of states

States of C⋆-subalgebras and nonunital C⋆-algebras extend to states of ambient unital C⋆-algebras:

* `TauCeti.surjOn_pullbackFunctional_stateSpace`: along an injective unital star homomorphism
  `f : A → B`, restriction of states `pullbackFunctional A f` maps the state space of `B` onto the
  state space of `A`.
* `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`: every state of a closed star
  subalgebra `S` of `A` (containing the unit of `A`) is the restriction of a state of `A`.
* `TauCeti.unitizeFunctional`, `TauCeti.unitizeFunctional_mem_stateSpace_iff`, and
  `TauCeti.unitizeFunctional_mem_stateSpace`: extending a functional `φ : WeakDual ℂ A` on a
  possibly nonunital C⋆-algebra `A` to `Unitization ℂ A` by `(w, a) ↦ w + φ a` yields a state of the
  minimal unitization if and only if `φ` is positive and contractive; conversely, restricting a
  state of `Unitization ℂ A` to `A` gives a positive contractive functional whose
  `unitizeFunctional` extension is the original state.

For unital embeddings, the proof takes a norm-preserving Hahn–Banach extension of the state along
`f`, by `LinearIsometry.exists_extension_norm_eq`, and reads off that it is a state from its value
`1` at the unit, by `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The extension applies
because an injective star homomorphism of C⋆-algebras is isometric. An extension of a state along a
general unital embedding need not be pure, multiplicative or unique.

## References

* B. Blackadar, *Operator Algebras*, II.6.3.1.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.3.9.
-/

public section

open Filter Set WeakDual
open scoped ComplexOrder ComplexStarModule Topology

namespace TauCeti

section UnitalEmbedding

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Extension of states.** Along an injective unital star homomorphism `f : A → B` of C⋆-algebras,
every state of `A` is the restriction `φ ∘ f` of a state `φ` of `B`. -/
theorem surjOn_pullbackFunctional_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
  intro φ hφ
  let i : A →ₗᵢ[ℂ] B := ⟨(f : A →ₗ[ℂ] B), NonUnitalStarAlgHom.norm_map f hf⟩
  obtain ⟨ψ, hψ, hnorm⟩ := i.exists_extension_norm_eq (toStrongDual φ)
  have hrestrict (a : A) : ψ (f a) = φ a := DFunLike.congr_fun hψ a
  have h1 : ψ 1 = 1 := by
    simpa [map_one f] using (hrestrict 1).trans (map_one_of_mem_stateSpace hφ)
  refine ⟨StrongDual.toWeakDual ψ, mem_stateSpace_iff_norm_eq_one_and_map_one.2
    ⟨hnorm.trans (norm_toStrongDual_of_mem_stateSpace hφ), by simpa⟩,
    DFunLike.ext _ _ fun a => by simpa using hrestrict a⟩

end UnitalEmbedding

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Extend a continuous linear functional `φ : WeakDual ℂ A` to the minimal unitization
`Unitization ℂ A` by sending `(w, a)` to `w + φ a`. -/
noncomputable def unitizeFunctional (φ : WeakDual ℂ A) : WeakDual ℂ (Unitization ℂ A) :=
  StrongDual.toWeakDual
    { toFun x := x.fst + φ x.snd
      map_add' x y := by
        simp only [Unitization.fst_add, Unitization.snd_add, map_add]
        ring
      map_smul' c x := by
        simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul, smul_eq_mul,
          RingHom.id_apply]
        ring
      cont := by fun_prop }

@[simp]
theorem unitizeFunctional_apply (φ : WeakDual ℂ A) (x : Unitization ℂ A) :
    unitizeFunctional φ x = x.fst + φ x.snd :=
  (rfl)

theorem unitizeFunctional_inr (φ : WeakDual ℂ A) (a : A) :
    unitizeFunctional φ (a : Unitization ℂ A) = φ a := by
  simp

theorem unitizeFunctional_one (φ : WeakDual ℂ A) :
    unitizeFunctional φ 1 = 1 := by
  simp

/-- Extending functionals to `Unitization ℂ A` via `unitizeFunctional` is injective. -/
theorem unitizeFunctional_injective :
    Function.Injective (unitizeFunctional (A := A)) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun a ↦ by simpa using DFunLike.congr_fun h (a : Unitization ℂ A)

@[simp]
theorem unitizeFunctional_inj {φ ψ : WeakDual ℂ A} :
    unitizeFunctional φ = unitizeFunctional ψ ↔ φ = ψ :=
  unitizeFunctional_injective.eq_iff

/-- `unitizeFunctional` is weak-* continuous. -/
@[fun_prop]
theorem continuous_unitizeFunctional :
    Continuous (unitizeFunctional (A := A)) :=
  continuous_of_continuous_eval fun x ↦ continuous_const.add (eval_continuous x.snd)

variable [PartialOrder A] [StarOrderedRing A]

@[simp]
theorem pullbackFunctional_inr_unitizeFunctional (φ : WeakDual ℂ A) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) (unitizeFunctional φ) = φ :=
  DFunLike.ext _ _ fun a ↦ by simp

/-- Restricting a functional `ψ` on `Unitization ℂ A` with `ψ 1 = 1` to `A` and re-extending by
`unitizeFunctional` recovers `ψ`. -/
theorem unitizeFunctional_pullbackFunctional_inr_of_map_one
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ 1 = 1) :
    unitizeFunctional (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ) = ψ := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  conv_rhs => rw [← x.inl_fst_add_inr_snd_eq]
  have hinl : (Unitization.inl x.fst : Unitization ℂ A) = x.fst • (1 : Unitization ℂ A) := by
    ext <;> simp
  rw [map_add, hinl, map_smul, hψ, smul_eq_mul, mul_one]
  simp

/-- Every state `ψ` of `Unitization ℂ A` is the `unitizeFunctional` extension of its restriction to
`A`. -/
theorem unitizeFunctional_pullbackFunctional_inr_of_mem_stateSpace
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A)) :
    unitizeFunctional (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ) = ψ :=
  unitizeFunctional_pullbackFunctional_inr_of_map_one (map_one_of_mem_stateSpace hψ)

private theorem unitizeFunctional_star_mul_self_nonneg {φ : WeakDual ℂ A}
    (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) (hnorm : ‖toStrongDual φ‖ ≤ 1) (y : Unitization ℂ A) :
    0 ≤ unitizeFunctional φ (star y * y) := by
  set w : ℂ := y.fst
  set b : A := y.snd
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h1 : Tendsto (fun e : A ↦ φ (e * b)) (CStarAlgebra.approximateUnit A) (𝓝 (φ b)) := by
    simpa [Function.comp_def] using
      ((toStrongDual φ).continuous.tendsto b).comp (hl.tendsto_mul_right b)
  have h2 : Tendsto (fun e : A ↦ φ (star b * e)) (CStarAlgebra.approximateUnit A)
      (𝓝 (φ (star b))) := by
    simpa [Function.comp_def] using
      ((toStrongDual φ).continuous.tendsto (star b)).comp (hl.tendsto_mul_left (star b))
  have hlim : Tendsto
      (fun e : A ↦ star w * w + star w * φ (e * b) + w * φ (star b * e) + φ (star b * b))
      (CStarAlgebra.approximateUnit A) (𝓝 (unitizeFunctional φ (star y * y))) := by
    have htarget : star w * w + star w * φ b + w * φ (star b) + φ (star b * b) =
        unitizeFunctional φ (star y * y) := by
      simp only [unitizeFunctional_apply, Unitization.fst_mul, Unitization.fst_star,
        Unitization.snd_mul, Unitization.snd_star, map_add, map_smul, smul_eq_mul, w, b]
      ring
    exact htarget ▸
      (((tendsto_const_nhds.add (h1.const_mul _)).add (h2.const_mul _)).add tendsto_const_nhds)
  refine ge_of_tendsto hlim ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he0 he1
  have he_sa : star e = e := he0.isSelfAdjoint.star_eq
  have he2_pos : 0 ≤ φ (e * e) := hpos (e * e) (by nth_rw 1 [← he_sa]; exact star_mul_self_nonneg e)
  have he2_le_one : φ (e * e) ≤ 1 := by
    have hle : ‖φ (e * e)‖ ≤ 1 :=
      ((toStrongDual φ).le_opNorm _).trans <|
        (mul_le_mul hnorm (norm_mul_le e e) (norm_nonneg _) zero_le_one).trans
          (by nlinarith [norm_nonneg e])
    exact Complex.le_def.2 ⟨(Complex.re_le_norm _).trans (by simpa using hle),
      by simpa using (Complex.nonneg_iff.1 he2_pos).2.symm⟩
  have hze : 0 ≤ φ (star (w • e + b) * (w • e + b)) := hpos _ (star_mul_self_nonneg _)
  have hmul : star (w • e + b) * (w • e + b) =
      (star w * w) • (e * e) + star w • (e * b) + w • (star b * e) + star b * b := by
    simp only [star_add, star_smul, he_sa, add_mul, mul_add, smul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm w (star w)]
    abel
  simp only [hmul, map_add, map_smul, smul_eq_mul] at hze
  have := mul_le_of_le_one_right (star_mul_self_nonneg w) he2_le_one
  refine hze.trans ?_
  gcongr

/-- The unitization extension `unitizeFunctional φ` is a state of `Unitization ℂ A` if and only if
`φ` is nonnegative on nonnegative elements and has norm at most one. -/
theorem unitizeFunctional_mem_stateSpace_iff {φ : WeakDual ℂ A} :
    unitizeFunctional φ ∈ stateSpace (Unitization ℂ A) ↔
      (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1 := by
  rw [mem_stateSpace_iff_map_one]
  refine ⟨fun ⟨hpos, _⟩ ↦ ⟨fun a ha ↦ ?_, ?_⟩, fun ⟨hpos, hnorm⟩ ↦ ⟨fun x hx ↦ ?_, by simp⟩⟩
  · simpa using hpos (a : Unitization ℂ A) (Unitization.inr_nonneg_iff.2 ha)
  · refine (toStrongDual φ).opNorm_le_bound zero_le_one fun a ↦ ?_
    have hstate : unitizeFunctional φ ∈ stateSpace (Unitization ℂ A) :=
      mem_stateSpace_iff_map_one.2 ⟨hpos, by simp⟩
    simpa [Unitization.norm_inr] using
      norm_apply_le_of_mem_stateSpace hstate (a : Unitization ℂ A)
  · rw [StarOrderedRing.nonneg_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact unitizeFunctional_star_mul_self_nonneg hpos hnorm y
    | zero => simp
    | add _ _ _ _ hu hv => simpa only [map_add] using add_nonneg hu hv

/-- Every state of `A` extends via `unitizeFunctional` to a state of `Unitization ℂ A`. -/
theorem unitizeFunctional_mem_stateSpace {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) :
    unitizeFunctional φ ∈ stateSpace (Unitization ℂ A) :=
  unitizeFunctional_mem_stateSpace_iff.2
    ⟨fun _ ↦ map_nonneg_of_mem_stateSpace hφ, (norm_toStrongDual_of_mem_stateSpace hφ).le⟩

/-- Restricting a state of `Unitization ℂ A` to `A` yields a positive functional on `A`. -/
theorem map_nonneg_pullbackFunctional_inr_of_mem_stateSpace
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A)) {a : A}
    (ha : 0 ≤ a) :
    0 ≤ pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ a :=
  (unitizeFunctional_mem_stateSpace_iff.1
    ((unitizeFunctional_pullbackFunctional_inr_of_mem_stateSpace hψ).symm ▸ hψ)).1 a ha

/-- Restricting a state of `Unitization ℂ A` to `A` yields a contractive functional on `A`. -/
theorem norm_toStrongDual_pullbackFunctional_inr_le_one_of_mem_stateSpace
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A)) :
    ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ ≤ 1 :=
  (unitizeFunctional_mem_stateSpace_iff.1
    ((unitizeFunctional_pullbackFunctional_inr_of_mem_stateSpace hψ).symm ▸ hψ)).2

end Unitization

end TauCeti

namespace StarSubalgebra

open TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Extension of states from a C⋆-subalgebra.** Every state of a closed star subalgebra `S` of a
unital C⋆-algebra `A`, containing the unit of `A`, is the restriction of a state of `A`. -/
theorem exists_mem_stateSpace_forall_apply_coe_eq (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ stateSpace S) :
    ∃ ψ ∈ stateSpace A, ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ := surjOn_pullbackFunctional_stateSpace S.subtype Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => (pullbackFunctional_apply S.subtype ψ s).symm⟩

end StarSubalgebra
