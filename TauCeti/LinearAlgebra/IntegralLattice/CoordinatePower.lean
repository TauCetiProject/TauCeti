/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Norm

/-!
# Coordinate powers of integral lattices

For an integral lattice `L` in `V` and a finite type `ι`, the coordinate power `L^ι` is the
orthogonal sum of `ι` copies of `L`: its carrier consists of the functions `ι → V` all of whose
values lie in `L`, and its form is the sum of the coordinate pairings,

```text
B(x, y) = ∑ i, L(x i, y i).
```

This is the lattice-level counterpart of the coordinate powers of finite bilinear and quadratic
modules: codes over the discriminant alphabet of `L` are glue subgroups for `L^ι`, as in the
constructions of lattices from copies of `A₂` or `D₄`. The coordinate power is
nondegenerate when `L` is, and even exactly when `L` is (for nonempty `ι`).

## Main declarations

* `TauCeti.IntegralLattice.coordinatePowerForm`: the summed ambient form on `ι → V`.
* `TauCeti.IntegralLattice.coordinatePower`: the coordinate power lattice.
* `TauCeti.IntegralLattice.nondegenerate_coordinatePower_iff`: nondegeneracy is inherited from
  and, for nonempty `ι`, detected by the factor.
* `TauCeti.IntegralLattice.isEven_coordinatePower_iff`: the same for evenness.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (ι : Type v) [Fintype ι]

/-- The ambient form of a coordinate power: the sum of the pairings of corresponding
coordinates. -/
def coordinatePowerForm : LinearMap.BilinForm ℚ (ι → V) :=
  ∑ i, L.form.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

/-- Evaluation of the coordinate-power form is the sum of the coordinate pairings. -/
@[simp]
theorem coordinatePowerForm_apply (x y : ι → V) :
    coordinatePowerForm L ι x y = ∑ i, L.form (x i) (y i) := by
  simp [coordinatePowerForm, LinearMap.sum_apply]

/-- Pairing with a function supported at one coordinate extracts that coordinate pairing. -/
@[simp]
theorem coordinatePowerForm_single_right [DecidableEq ι] (x : ι → V) (i : ι) (v : V) :
    (∑ j, L.form (x j) ((Pi.single i v : ι → V) j)) = L.form (x i) v := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- Pairing a function supported at one coordinate with an arbitrary function extracts that
coordinate pairing. -/
@[simp]
theorem coordinatePowerForm_single_left [DecidableEq ι] (i : ι) (v : V) (y : ι → V) :
    (∑ j, L.form ((Pi.single i v : ι → V) j) (y j)) = L.form v (y i) := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero, LinearMap.zero_apply]
  · simp

omit [Fintype ι] in
/-- The functions all of whose values lie in a full integral carrier form a full integral carrier
of the function space. -/
private theorem isLattice_pi [Finite ι] :
    (Submodule.pi Set.univ fun _ : ι ↦ L.carrier).IsLattice ℚ := by
  classical
  cases nonempty_fintype ι
  constructor
  · exact Submodule.fg_pi fun _ ↦ (Submodule.IsLattice.fg (A := ℚ))
  · rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hx : x i ∈ Submodule.span ℚ (L.carrier : Set V) := by
      rw [Submodule.IsLattice.span_eq_top]
      exact Submodule.mem_top
    have hmap : Submodule.map (LinearMap.single ℚ (fun _ : ι ↦ V) i)
        (Submodule.span ℚ (L.carrier : Set V)) ≤
        Submodule.span ℚ (Submodule.pi Set.univ fun _ : ι ↦ L.carrier : Set (ι → V)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact Submodule.subset_span (Submodule.le_comap_single_pi (fun _ ↦ L.carrier) hv)
    exact hmap (Submodule.mem_map_of_mem hx)

/-- The coordinate power `L^ι` of an integral lattice: the orthogonal sum of `ι` copies of `L`,
with carrier the functions `ι → V` whose values all lie in `L`. -/
def coordinatePower : IntegralLattice (ι → V) where
  carrier := Submodule.pi Set.univ fun _ ↦ L.carrier
  form := coordinatePowerForm L ι
  isLattice := isLattice_pi L ι
  isSymm := ⟨fun x y ↦ by
    simp only [coordinatePowerForm_apply]
    exact Finset.sum_congr rfl fun i _ ↦ L.isSymm.eq (x i) (y i)⟩
  le_dual := by
    intro x hx
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [coordinatePowerForm_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      L.le_dual (hx i (Set.mem_univ i)) (y i) (hy i (Set.mem_univ i))

/-- The carrier of a coordinate power consists of the functions with values in `L`. -/
@[simp]
theorem coordinatePower_carrier :
    (L.coordinatePower ι).carrier = Submodule.pi Set.univ fun _ ↦ L.carrier :=
  (rfl)

/-- The form of a coordinate power is the summed coordinate form. -/
@[simp]
theorem coordinatePower_form : (L.coordinatePower ι).form = coordinatePowerForm L ι :=
  (rfl)

/-- A function lies in the coordinate power exactly when each of its values lies in `L`. -/
theorem mem_coordinatePower_carrier_iff (x : ι → V) :
    x ∈ (L.coordinatePower ι).carrier ↔ ∀ i, x i ∈ L.carrier := by
  simp

/-- A function supported at one coordinate, with value in `L`, lies in the coordinate power. -/
theorem single_mem_coordinatePower_carrier [DecidableEq ι] (i : ι) {v : V}
    (hv : v ∈ L.carrier) : Pi.single i v ∈ (L.coordinatePower ι).carrier :=
  Submodule.le_comap_single_pi (fun _ ↦ L.carrier) hv

/-- The norm on a coordinate power is the sum of the coordinate norms. -/
@[simp]
theorem norm_coordinatePower_apply (x : ι → V) :
    (L.coordinatePower ι).norm x = ∑ i, L.norm (x i) := by
  simp [norm_apply]

/-! ## Nondegeneracy -/

/-- A vector which pairs trivially with every function is zero in every coordinate, provided the
factor form is nondegenerate. -/
private theorem eq_zero_of_forall_coordinatePowerForm (hL : L.form.Nondegenerate)
    {x : ι → V} (hx : ∀ y, coordinatePowerForm L ι x y = 0) : x = 0 := by
  classical
  funext i
  apply hL.1 (x i)
  intro v
  rw [← coordinatePowerForm_single_right L ι x i v, ← coordinatePowerForm_apply]
  exact hx _

/-- The coordinate-power form is nondegenerate when the factor form is, and conversely when the
index type is nonempty. -/
theorem nondegenerate_coordinatePower_iff [Nonempty ι] :
    (L.coordinatePower ι).form.Nondegenerate ↔ L.form.Nondegenerate := by
  classical
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine L.isSymm.isRefl.nondegenerate_iff_separatingLeft.mpr fun v hv ↦ ?_
    have hzero : (Pi.single i v : ι → V) = 0 :=
      h.1 _ fun y ↦ by
        rw [coordinatePower_form, coordinatePowerForm_apply, coordinatePowerForm_single_left]
        exact hv (y i)
    simpa using congrFun hzero i
  · intro hL
    exact (L.coordinatePower ι).isSymm.isRefl.nondegenerate_iff_separatingLeft.mpr fun _ hx ↦
      eq_zero_of_forall_coordinatePowerForm L ι hL hx

/-- A coordinate power of a nondegenerate integral lattice is nondegenerate. -/
instance instIsNondegenerateCoordinatePower [L.IsNondegenerate] :
    (L.coordinatePower ι).IsNondegenerate :=
  ⟨(L.coordinatePower ι).isSymm.isRefl.nondegenerate_iff_separatingLeft.mpr fun _ hx ↦
    eq_zero_of_forall_coordinatePowerForm L ι L.form_nondegenerate hx⟩

/-! ## Evenness -/

/-- A coordinate power of an even lattice is even. -/
theorem IsEven.coordinatePower {L : IntegralLattice V} (hL : L.IsEven) :
    (L.coordinatePower ι).IsEven := by
  rw [isEven_iff_forall_norm]
  intro x
  choose z hz using fun i ↦
    hL.exists_norm_eq_two_mul ⟨(x : ι → V) i, (L.mem_coordinatePower_carrier_iff ι _).mp x.2 i⟩
  refine ⟨∑ i, z i, ?_⟩
  rw [norm_coordinatePower_apply]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hz i

/-- A coordinate power over a nonempty index type is even exactly when the factor is even. -/
theorem isEven_coordinatePower_iff [Nonempty ι] :
    (L.coordinatePower ι).IsEven ↔ L.IsEven := by
  classical
  refine ⟨fun h ↦ ?_, fun hL ↦ hL.coordinatePower ι⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [isEven_iff_forall_norm] at h ⊢
  intro v
  obtain ⟨z, hz⟩ := h ⟨_, L.single_mem_coordinatePower_carrier ι i v.2⟩
  refine ⟨z, ?_⟩
  rw [← hz, norm_coordinatePower_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

end TauCeti.IntegralLattice
