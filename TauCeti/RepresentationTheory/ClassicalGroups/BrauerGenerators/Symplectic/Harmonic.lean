/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Contraction
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Basic

/-!
# Symplectic harmonic tensors

The harmonic tensors in a tensor power of the standard symplectic module are the common kernel
of all pairwise contractions against its alternating form. The contraction maps take values in
tensor products over the remaining slots, so they genuinely lower tensor degree by two rather
than contracting and reinserting a cup.

This file proves stability under the diagonal symplectic action and permutations of slots,
and packages the former as a subrepresentation. Pure tensors with pairwise symplectically
orthogonal factors are harmonic; in particular every pure power is harmonic. These subspaces
supply the traceless parts used in the symplectic Weyl construction and the trace filtration.
No irreducibility or splitting of that filtration is asserted here.

The definition parallels `TauCeti.harmonicTensors`, but uses the contraction maps themselves,
so it needs neither a nonzero dimension nor an invertible loop value.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] (n d : ℕ)

/-- The symplectic harmonic tensors: the common kernel of contractions of every pair of distinct
slots against the standard alternating form. -/
noncomputable def symplecticHarmonicTensors :
    Submodule k (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  ⨅ i : Fin d, ⨅ j : Fin d, ⨅ hij : i ≠ j,
    LinearMap.ker ((stdSymplecticBilinForm k n).contractTensorPair i j hij)

/-- The defining infimum of kernels of the symplectic trace maps. -/
theorem symplecticHarmonicTensors_def :
    symplecticHarmonicTensors k n d =
      ⨅ i : Fin d, ⨅ j : Fin d, ⨅ hij : i ≠ j,
        LinearMap.ker ((stdSymplecticBilinForm k n).contractTensorPair i j hij) :=
  (rfl)

variable {k n d}

/-- A tensor is symplectic harmonic exactly when every pair contraction vanishes. -/
@[simp]
theorem mem_symplecticHarmonicTensors {x : ⨂[k]^d ((Fin n ⊕ Fin n) → k)} :
    x ∈ symplecticHarmonicTensors k n d ↔
      ∀ (i j : Fin d) (hij : i ≠ j),
        (stdSymplecticBilinForm k n).contractTensorPair i j hij x = 0 := by
  simp only [symplecticHarmonicTensors_def, Submodule.mem_iInf, LinearMap.mem_ker]

/-- A submodule is harmonic exactly when every pair contraction kills it. -/
theorem le_symplecticHarmonicTensors_iff
    {p : Submodule k (⨂[k]^d ((Fin n ⊕ Fin n) → k))} :
    p ≤ symplecticHarmonicTensors k n d ↔
      ∀ (i j : Fin d) (hij : i ≠ j),
        p ≤ LinearMap.ker ((stdSymplecticBilinForm k n).contractTensorPair i j hij) := by
  simp only [symplecticHarmonicTensors_def, le_iInf_iff]

/-- A pure tensor of pairwise symplectically orthogonal vectors is harmonic. -/
theorem tprod_mem_symplecticHarmonicTensors {v : Fin d → ((Fin n ⊕ Fin n) → k)}
    (hv : ∀ i j : Fin d, i ≠ j → stdSymplecticBilinForm k n (v i) (v j) = 0) :
    PiTensorProduct.tprod k v ∈ symplecticHarmonicTensors k n d := by
  simp only [mem_symplecticHarmonicTensors, LinearMap.contractTensorPair_tprod]
  intro i j hij
  rw [hv i j hij, zero_smul]

/-- Every pure power is symplectic harmonic, since the pairing is alternating. -/
theorem tprod_const_mem_symplecticHarmonicTensors (v : (Fin n ⊕ Fin n) → k) :
    PiTensorProduct.tprod k (fun _ : Fin d => v) ∈ symplecticHarmonicTensors k n d :=
  tprod_mem_symplecticHarmonicTensors fun _ _ _ => isAlt_stdSymplecticBilinForm k n v

/-- There are no trace conditions in tensor degrees zero and one. -/
theorem symplecticHarmonicTensors_eq_top_of_le_one (hd : d ≤ 1) :
    symplecticHarmonicTensors k n d = ⊤ := by
  refine eq_top_iff.mpr fun x _ => mem_symplecticHarmonicTensors.mpr fun i j hij => ?_
  have hi := i.isLt
  have hj := j.isLt
  exact (hij (Fin.ext (by omega))).elim

/-- On two strands, the harmonic tensors are exactly the kernel of the symplectic cap. -/
theorem symplecticHarmonicTensors_two_eq_ker_symplecticCap :
    symplecticHarmonicTensors k n 2 = LinearMap.ker (symplecticCap k n) := by
  have hpair (i j : Fin 2) (hij : i ≠ j) :
      LinearMap.ker ((stdSymplecticBilinForm k n).contractTensorPair i j hij) =
        LinearMap.ker (symplecticCap k n) := by
    let : IsEmpty {a : Fin 2 // a ≠ i ∧ a ≠ j} := ⟨fun ⟨a, ha⟩ => by
      simp only [ne_eq, Fin.ext_iff] at hij ha
      omega⟩
    let e := PiTensorProduct.isEmptyEquiv (R := k)
      (s := fun _ : {a : Fin 2 // a ≠ i ∧ a ≠ j} => (Fin n ⊕ Fin n) → k) _
    have ht (v : {a : Fin 2 // a ≠ i ∧ a ≠ j} → ((Fin n ⊕ Fin n) → k)) :
        e (PiTensorProduct.tprod k v) = 1 := PiTensorProduct.isEmptyEquiv_apply_tprod _ v
    have he : e.toLinearMap ∘ₗ (stdSymplecticBilinForm k n).contractTensorPair i j hij =
        (if i = 0 then (1 : k) else -1) • symplecticCap k n := by
      apply PiTensorProduct.ext
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearMap.contractTensorPair_tprod, LinearEquiv.coe_coe, map_smul,
        ht, smul_eq_mul, mul_one, LinearMap.smul_apply, symplecticCap_tprod]
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simp
      · simpa using ((isAlt_stdSymplecticBilinForm k n).neg_eq (v 0) (v 1)).symm
      · exact (hij rfl).elim
    ext x
    have hezero := e.map_eq_zero_iff
      (x := (stdSymplecticBilinForm k n).contractTensorPair i j hij x)
    have h := LinearMap.congr_fun he x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe] at h
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hezero, h]
    split_ifs <;> simp
  ext x
  simp only [mem_symplecticHarmonicTensors, ← LinearMap.mem_ker, hpair]
  exact ⟨fun h => h 0 1 (by decide), fun h _ _ _ => h⟩

/-- The diagonal symplectic action preserves the common kernel of the trace maps. -/
theorem tensorPower_mem_symplecticHarmonicTensors
    (g : Matrix.symplecticGroup (Fin n) k)
    {x : ⨂[k]^d ((Fin n ⊕ Fin n) → k)} (hx : x ∈ symplecticHarmonicTensors k n d) :
    (stdSymplecticRep k n).tensorPower d g x ∈ symplecticHarmonicTensors k n d := by
  refine mem_symplecticHarmonicTensors.mpr fun i j hij => ?_
  have hform (v w : (Fin n ⊕ Fin n) → k) :
      stdSymplecticBilinForm k n (stdSymplecticRep k n g v) (stdSymplecticRep k n g w) =
        stdSymplecticBilinForm k n v w := by
    simpa only [stdSymplecticRep_apply, LinearMap.BilinForm.comp_apply] using
      LinearMap.congr_fun
        (LinearMap.congr_fun (stdSymplecticBilinForm_comp_stdSymplecticRep k n g) v) w
  have h := LinearMap.congr_fun
    ((stdSymplecticBilinForm k n).contractTensorPair_comp_map i j hij
      (stdSymplecticRep k n g) hform) x
  simpa only [Representation.tensorPower_apply, LinearMap.comp_apply,
    mem_symplecticHarmonicTensors.mp hx i j hij, map_zero] using h

/-- Renaming tensor slots preserves symplectic harmonicity. This also gives stability under the
sign-twisted permutation action used for symplectic Brauer diagrams. -/
theorem reindex_mem_symplecticHarmonicTensors (σ : Equiv.Perm (Fin d))
    {x : ⨂[k]^d ((Fin n ⊕ Fin n) → k)} (hx : x ∈ symplecticHarmonicTensors k n d) :
    PiTensorProduct.reindex k (fun _ : Fin d => (Fin n ⊕ Fin n) → k) σ x ∈
      symplecticHarmonicTensors k n d := by
  refine mem_symplecticHarmonicTensors.mpr fun i j hij => ?_
  obtain ⟨a, rfl⟩ := σ.surjective i
  obtain ⟨b, rfl⟩ := σ.surjective j
  have hab : a ≠ b := fun h => hij (congrArg σ h)
  simpa only [mem_symplecticHarmonicTensors.mp hx, map_zero] using
    (stdSymplecticBilinForm k n).contractTensorPair_reindex a b hab σ x

variable (k n d)

/-- Symplectic harmonic tensors as a subrepresentation of the diagonal tensor-power action. -/
noncomputable def symplecticHarmonicTensorsSubrep :
    Subrepresentation ((stdSymplecticRep k n).tensorPower d) where
  toSubmodule := symplecticHarmonicTensors k n d
  apply_mem_toSubmodule g _ hx := tensorPower_mem_symplecticHarmonicTensors g hx

@[simp]
theorem symplecticHarmonicTensorsSubrep_toSubmodule :
    (symplecticHarmonicTensorsSubrep k n d).toSubmodule =
      symplecticHarmonicTensors k n d :=
  (rfl)

end TauCeti
