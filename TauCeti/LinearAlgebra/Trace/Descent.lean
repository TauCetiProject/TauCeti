/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: tensor products, intermediate fields and the central simple algebra classes occur in
-- the exported statements.
public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.SimpleRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
-- Non-public: used only inside proofs.
import Mathlib.Algebra.Central.End
import Mathlib.RingTheory.SimpleRing.Congr
import TauCeti.Algebra.CentralSimple.End
import TauCeti.Algebra.CentralSimple.BaseChange
import TauCeti.LinearAlgebra.Trace.Nondegenerate

/-!
# Descending `End_K(V)` along traces

Let `F ⊆ K` be a subfield and `B` an `F`-subalgebra of `End_K(V)`, `V` finite-dimensional over
`K`. If `B` spans `End_K(V)` over `K` and every element of `B` has trace in `F`, then `B` is an
`F`-form of `End_K(V)`: multiplication `K ⊗_F B → End_K(V)` is an isomorphism. Consequently `B` is
central over `F`, simple when `V ≠ 0`, and of dimension `(dim_K V)²` over `F`.

A `K`-basis `b` of `End_K(V)` taken inside `B` has Gram matrix `(tr (bᵢ bⱼ))` with entries in `F`,
invertible because the trace pairing on `End_K(V)` is nondegenerate. The coordinates of `x ∈ B`
solve a linear system with this matrix and right-hand side `(tr (x bⱼ))` in `F`, so they lie in
`F`, and `B` is contained in the `F`-span of `b`. Hence `dim_F B ≤ (dim_K V)²`, while
`K ⊗_F B → End_K(V)` is onto, so it is an isomorphism by counting dimensions.

This is the descent behind the image algebra of an absolutely irreducible representation,
`TauCeti/RepresentationTheory/ImageAlgebra.lean`.

## Main results

* `Module.End.baseChangeSubalgebraAlgEquiv`: a spanning subalgebra with traces in `F` is an
  `F`-form of `End_K(V)`.
* `Module.End.finrank_subalgebra_of_trace_mem`: it has dimension `(dim_K V)²` over `F`.
* `Module.End.isCentral_subalgebra_of_trace_mem`, `Module.End.isSimpleRing_subalgebra_of_trace_mem`:
  it is central simple over `F`.
-/

public section

open Module
open scoped TensorProduct

namespace Module.End

variable {k K V : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : IntermediateField k K}

/-- The trace pairing against a spanning family is injective: if `tr (bᵢ x) = 0` for every member
`bᵢ` of a family spanning `End_K(V)`, then `x = 0`. -/
private theorem eq_zero_of_forall_trace_mul_eq_zero {ι : Type*} {b : ι → End K V}
    (hb : Submodule.span K (Set.range b) = ⊤) {x : End K V}
    (hx : ∀ i, LinearMap.trace K V (b i * x) = 0) : x = 0 := by
  refine LinearMap.forall_trace_mul_eq_zero_iff.mp fun y => ?_
  have hy : y ∈ Submodule.span K (Set.range b) := hb ▸ Submodule.mem_top
  rw [LinearMap.trace_mul_comm]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
  | zero => simp
  | add z w _ _ hz hw => simp [add_mul, hz, hw]
  | smul a z _ hz => simp [hz]

/-- The Gram matrix of the trace pairing on a basis of `End_K(V)` is invertible. -/
private theorem det_trace_mul_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K (End K V)) :
    (Matrix.of fun i j => LinearMap.trace K V (b i * b j)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hx : ∑ j, v j • b j = 0 := by
    refine eq_zero_of_forall_trace_mul_eq_zero b.span_eq fun i => ?_
    have := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  exact hv (funext fun j => Fintype.linearIndependent_iff.mp b.linearIndependent v hx j)

/-- **Coordinates descend.** Let `B` be an `F`-subalgebra of `End_K(V)` all of whose elements have
trace in `F`, and `b` a `K`-basis of `End_K(V)` with members in `B`. Then every element of `B` is an
`F`-linear combination of `b`. -/
private theorem mem_span_of_trace_mem {ι : Type*} [Finite ι] (B : Subalgebra F (End K V))
    (htr : ∀ x ∈ B, LinearMap.trace K V x ∈ F) (b : Basis ι K (End K V)) (hbB : ∀ i, b i ∈ B)
    {x : End K V} (hx : x ∈ B) : x ∈ Submodule.span F (Set.range b) := by
  classical
  have := Fintype.ofFinite ι
  -- The Gram matrix and the right-hand side, with entries in `F`.
  let G' : Matrix ι ι F := Matrix.of fun i j =>
    ⟨LinearMap.trace K V (b i * b j), htr _ (B.mul_mem (hbB i) (hbB j))⟩
  let t' : ι → F := fun j => ⟨LinearMap.trace K V (x * b j), htr _ (B.mul_mem hx (hbB j))⟩
  have hG : G'.map (algebraMap F K) = Matrix.of fun i j => LinearMap.trace K V (b i * b j) := rfl
  have hdetG : (G'.map (algebraMap F K)).det ≠ 0 := hG ▸ det_trace_mul_ne_zero b
  have hdet : algebraMap F K G'.det ≠ 0 := by
    rwa [RingHom.map_det]
  have hdet' : IsUnit G'.det := isUnit_iff_ne_zero.mpr fun h => hdet (by simp [h])
  -- The coordinates of `x` solve `c ᵥ* G = t`.
  set c := b.repr x
  have hc : Matrix.vecMul c (G'.map (algebraMap F K)) = (algebraMap F K) ∘ t' := by
    funext j
    have hxj : LinearMap.trace K V (x * b j) =
        LinearMap.trace K V ((∑ i, c i • b i) * b j) := by rw [b.sum_repr x]
    simp only [Matrix.vecMul, dotProduct, hG, Matrix.of_apply, Function.comp_apply, t',
      IntermediateField.algebraMap_apply, hxj, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
      smul_eq_mul]
  let c' : ι → F := Matrix.vecMul t' G'⁻¹
  have hcc' : c = (algebraMap F K) ∘ c' := by
    have hc' : Matrix.vecMul ((algebraMap F K) ∘ c') (G'.map (algebraMap F K)) =
        (algebraMap F K) ∘ t' := by
      funext j
      rw [Function.comp_apply, ← RingHom.map_vecMul, Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul _ hdet', Matrix.vecMul_one]
    set G := G'.map (algebraMap F K)
    have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdetG
    calc c = Matrix.vecMul (Matrix.vecMul c G) G⁻¹ := by
          rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]
      _ = _ := by
          rw [hc, ← hc', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]
  have hx' : x = ∑ i, c' i • b i := by
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c' i) (b i)]
    exact congrArg (· • b i) (congrFun hcc' i)
  rw [hx']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [FiniteDimensional K V] in
/-- The multiplication map `K ⊗_F B → End_K(V)` of an `F`-subalgebra `B`. -/
noncomputable def baseChangeSubalgebraAlgHom (B : Subalgebra F (End K V)) :
    K ⊗[F] B →ₐ[K] End K V :=
  Algebra.TensorProduct.lift (Algebra.ofId K (End K V)) B.val fun a _ => by
    rw [Algebra.ofId_apply]
    exact Algebra.commute_algebraMap_left a _

omit [FiniteDimensional K V] in
@[simp]
theorem baseChangeSubalgebraAlgHom_tmul (B : Subalgebra F (End K V)) (a : K) (x : B) :
    baseChangeSubalgebraAlgHom B (a ⊗ₜ x) = a • (x : End K V) := by
  rw [baseChangeSubalgebraAlgHom, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

variable (B : Subalgebra F (End K V)) (hspan : Submodule.span K (B : Set (End K V)) = ⊤)
  (htr : ∀ x ∈ B, LinearMap.trace K V x ∈ F)

include hspan htr in
/-- A subalgebra spanning `End_K(V)` with traces in `F` lies in the `F`-span of a `K`-basis of
`End_K(V)`; in particular it is finite-dimensional over `F` of dimension at most `n²`. -/
private theorem exists_basis_le_span :
    ∃ (T : Set (End K V)) (_ : Fintype T) (b : Basis T K (End K V)),
      Subalgebra.toSubmodule B ≤ Submodule.span F (Set.range b) := by
  obtain ⟨T, hTB, hTspan, hTli⟩ := exists_linearIndependent K (B : Set (End K V))
  have hfin : T.Finite := hTli.setFinite
  let _ : Fintype T := hfin.fintype
  let b : Basis T K (End K V) := Basis.mk hTli (by rw [Subtype.range_coe, hTspan, hspan])
  refine ⟨T, inferInstance, b, fun x hx => ?_⟩
  exact mem_span_of_trace_mem B htr b (fun i => by simpa [b] using hTB i.property) hx

include hspan htr in
/-- A subalgebra spanning `End_K(V)` with traces in `F` is finite-dimensional over `F`. -/
theorem finiteDimensional_subalgebra_of_trace_mem : FiniteDimensional F B := by
  obtain ⟨T, _, b, hle⟩ := exists_basis_le_span B hspan htr
  have : FiniteDimensional F (Submodule.span F (Set.range b)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range b)
  exact Submodule.finiteDimensional_of_le hle

include hspan htr in
/-- **A spanning subalgebra with traces in `F` is an `F`-form of `End_K(V)`**: the multiplication
map `K ⊗_F B → End_K(V)` is bijective. -/
theorem bijective_baseChangeSubalgebraAlgHom :
    Function.Bijective (baseChangeSubalgebraAlgHom B) := by
  have := finiteDimensional_subalgebra_of_trace_mem B hspan htr
  have hsurj : Function.Surjective (baseChangeSubalgebraAlgHom B) := by
    rw [← AlgHom.range_eq_top, eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span K (B : Set (End K V)) := hspan ▸ Submodule.mem_top
    change y ∈ Subalgebra.toSubmodule (baseChangeSubalgebraAlgHom B).range
    refine Submodule.span_le.mpr (fun z hz => ?_) hy
    exact ⟨1 ⊗ₜ ⟨z, hz⟩, by simp⟩
  obtain ⟨T, _, b, hle⟩ := exists_basis_le_span B hspan htr
  have hle' : finrank F B ≤ finrank K (End K V) := by
    have : FiniteDimensional F (Submodule.span F (Set.range b)) :=
      FiniteDimensional.span_of_finite F (Set.finite_range b)
    rw [← Subalgebra.finrank_toSubmodule, finrank_eq_card_basis b]
    exact (Submodule.finrank_mono hle).trans (finrank_range_le_card b)
  have hge : finrank K (End K V) ≤ finrank F B := by
    rw [← Module.finrank_baseChange (R := K) (S := F) (M' := B)]
    exact LinearMap.finrank_le_finrank_of_surjective
      (f := (baseChangeSubalgebraAlgHom B).toLinearMap) hsurj
  have heq : finrank K (K ⊗[F] B) = finrank K (End K V) := by
    rw [Module.finrank_baseChange]; omega
  refine ⟨?_, hsurj⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq
    (f := (baseChangeSubalgebraAlgHom B).toLinearMap)).mpr hsurj

/-- **A spanning subalgebra with traces in `F` is an `F`-form of `End_K(V)`**: multiplication
`K ⊗_F B ≃ End_K(V)`. -/
noncomputable def baseChangeSubalgebraAlgEquiv : K ⊗[F] B ≃ₐ[K] End K V :=
  AlgEquiv.ofBijective (baseChangeSubalgebraAlgHom B)
    (bijective_baseChangeSubalgebraAlgHom B hspan htr)

@[simp]
theorem baseChangeSubalgebraAlgEquiv_tmul (a : K) (x : B) :
    baseChangeSubalgebraAlgEquiv B hspan htr (a ⊗ₜ x) = a • (x : End K V) :=
  baseChangeSubalgebraAlgHom_tmul B a x

include hspan htr in
/-- A spanning subalgebra with traces in `F` has dimension `(dim_K V)²` over `F`. -/
theorem finrank_subalgebra_of_trace_mem : finrank F B = finrank K V ^ 2 := by
  have := finiteDimensional_subalgebra_of_trace_mem B hspan htr
  rw [← Module.finrank_baseChange (R := K),
    (baseChangeSubalgebraAlgEquiv B hspan htr).toLinearEquiv.finrank_eq,
    Module.finrank_linearMap, sq]

include hspan htr in
/-- A spanning subalgebra with traces in `F` is central over `F`. -/
theorem isCentral_subalgebra_of_trace_mem : Algebra.IsCentral F B :=
  have : Algebra.IsCentral K (K ⊗[F] B) := ⟨fun x hx => by
    let e := baseChangeSubalgebraAlgEquiv B hspan htr
    have hx' : e x ∈ Subalgebra.center K (End K V) :=
      (MulEquivClass.apply_mem_center_iff e).mpr hx
    obtain ⟨a, ha⟩ := Algebra.IsCentral.out hx'
    exact ⟨a, e.injective (by simpa using ha)⟩⟩
  Algebra.IsCentral.of_baseChange (L := K)

include hspan htr in
/-- A spanning subalgebra with traces in `F` is a simple ring when `V ≠ 0`. -/
theorem isSimpleRing_subalgebra_of_trace_mem [Nontrivial V] : IsSimpleRing B :=
  have : IsSimpleRing (K ⊗[F] B) :=
    IsSimpleRing.of_ringEquiv (baseChangeSubalgebraAlgEquiv B hspan htr).symm.toRingEquiv
      inferInstance
  IsSimpleRing.of_baseChange (K := F) (L := K) (A := B)

end Module.End
