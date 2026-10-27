/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# Orthogonal sums of finite families of integral lattices

For a finite family of integral lattices `L i` in rational vector spaces `V i`, the orthogonal sum
`⊥ i, L i` is the integral lattice in `Π i, V i` whose carrier consists of the families with
`x i ∈ L i` for every `i`, and whose form is the sum of the coordinate forms,

```text
B(x, y) = ∑ i, L_i(x i, y i).
```

This is the `ι`-indexed analogue of the binary orthogonal sum
`TauCeti.IntegralLattice.orthogonalSum`, and the lattice-level counterpart of the orthogonal sum
`TauCeti.FiniteQuadraticModule.pi` of finite quadratic modules.  Unlike a coordinate power, the
summands may live in different ambient spaces: this is the shape of an orthogonal sum of root
lattices of an ordered list of Dynkin components, indexed by `Fin n`, as used in gluing
constructions of lattices.  The coordinate power `TauCeti.IntegralLattice.coordinatePower` is the
orthogonal sum of a constant family.

The orthogonal sum is nondegenerate when every summand is, and it is even, respectively positive
definite, exactly when every summand is.  Its rank is the sum of the ranks.  It is functorial in
the summands and invariant under reindexing the family, which is how a permutation of the
components of a reducible root system acts on the orthogonal sum of their root lattices.

## Main declarations

* `TauCeti.IntegralLattice.piForm`: the summed ambient form on `Π i, V i`.
* `TauCeti.IntegralLattice.pi`: the orthogonal sum of a finite family of integral lattices.
* `TauCeti.IntegralLattice.isEven_pi_iff`, `TauCeti.IntegralLattice.isPosDef_pi_iff`: evenness
  and positive-definiteness are detected summandwise.
* `TauCeti.IntegralLattice.finrank_pi`: the rank of the orthogonal sum is the sum of the ranks.
* `TauCeti.IntegralLattice.Isometry.pi`: the orthogonal sum of a family of isometries.
* `TauCeti.IntegralLattice.Isometry.piCongrLeft`: the isometry `⊥ k, L (σ k) ≅ ⊥ i, L i` induced
  by an equivalence `σ : κ ≃ ι` of index types.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCeti/LinearAlgebra/IntegralLattice/CoordinatePower.lean`: the coordinate power `L^ι`, the
  constant-family case `pi fun _ : ι ↦ L`.
-/

public section

namespace TauCeti.IntegralLattice

universe u v w x

variable {ι : Type v} [Fintype ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℚ (V i)]
variable (L : ∀ i, IntegralLattice (V i))

/-! ## The summed form -/

/-- The ambient form of an orthogonal sum: the sum of the pairings of corresponding
coordinates. -/
def piForm : LinearMap.BilinForm ℚ (∀ i, V i) :=
  ∑ i, (L i).form.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

/-- Evaluation of the orthogonal-sum form is the sum of the coordinate pairings. -/
@[simp]
theorem piForm_apply (x y : ∀ i, V i) : piForm L x y = ∑ i, (L i).form (x i) (y i) := by
  simp [piForm, LinearMap.sum_apply]

/-- Pairing with a family supported at one index extracts that coordinate pairing. -/
theorem piForm_single_right [DecidableEq ι] (x : ∀ i, V i) (i : ι) (v : V i) :
    piForm L x (Pi.single i v) = (L i).form (x i) v := by
  rw [piForm_apply, Finset.sum_eq_single i (fun j _ hji ↦ by
    rw [Pi.single_eq_of_ne hji, map_zero]) (by simp), Pi.single_eq_same]

/-- Pairing a family supported at one index with an arbitrary family extracts that coordinate
pairing. -/
theorem piForm_single_left [DecidableEq ι] (i : ι) (v : V i) (y : ∀ i, V i) :
    piForm L (Pi.single i v) y = (L i).form v (y i) := by
  rw [piForm_apply, Finset.sum_eq_single i (fun j _ hji ↦ by
    rw [Pi.single_eq_of_ne hji, map_zero, LinearMap.zero_apply]) (by simp), Pi.single_eq_same]

/-! ## The orthogonal sum -/

/-- **The orthogonal sum of a finite family of integral lattices**: the integral lattice in
`Π i, V i` whose carrier consists of the families with `x i ∈ L i` for every `i`, with the summed
form `∑ i, L_i(x i, y i)`. -/
def pi : IntegralLattice (∀ i, V i) where
  carrier := Submodule.pi Set.univ fun i ↦ (L i).carrier
  form := piForm L
  isLattice := inferInstance
  isSymm := ⟨fun x y ↦ by
    simp only [piForm_apply]
    exact Finset.sum_congr rfl fun i _ ↦ (L i).isSymm.eq (x i) (y i)⟩
  le_dual := by
    intro x hx
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [piForm_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      (L i).le_dual (hx i (Set.mem_univ i)) (y i) (hy i (Set.mem_univ i))

/-- The carrier of an orthogonal sum consists of the families with values in the summands. -/
@[simp]
theorem pi_carrier : (pi L).carrier = Submodule.pi Set.univ fun i ↦ (L i).carrier :=
  (rfl)

/-- The form of an orthogonal sum is the summed coordinate form. -/
@[simp]
theorem pi_form : (pi L).form = piForm L :=
  (rfl)

/-- A family lies in the orthogonal sum exactly when each of its values lies in its summand. -/
theorem mem_pi_carrier_iff (x : ∀ i, V i) : x ∈ (pi L).carrier ↔ ∀ i, x i ∈ (L i).carrier := by
  simp

/-- A family supported at one index, with value in that summand, lies in the orthogonal sum. -/
theorem single_mem_pi_carrier [DecidableEq ι] (i : ι) {v : V i} (hv : v ∈ (L i).carrier) :
    Pi.single i v ∈ (pi L).carrier :=
  Submodule.le_comap_single_pi (fun i ↦ (L i).carrier) hv

/-- The norm on an orthogonal sum is the sum of the coordinate norms. -/
@[simp]
theorem norm_pi_apply (x : ∀ i, V i) : (pi L).norm x = ∑ i, (L i).norm (x i) := by
  simp [norm_apply]

/-! ## Nondegeneracy -/

/-- A vector which pairs trivially with every family is zero, provided every summand form is
nondegenerate. -/
private theorem eq_zero_of_forall_piForm (hL : ∀ i, (L i).form.Nondegenerate)
    {x : ∀ i, V i} (hx : ∀ y, piForm L x y = 0) : x = 0 := by
  classical
  funext i
  exact (hL i).1 (x i) fun v ↦ by rw [← piForm_single_right]; exact hx _

/-- The orthogonal-sum form is nondegenerate exactly when every summand form is. -/
theorem nondegenerate_pi_iff :
    (pi L).form.Nondegenerate ↔ ∀ i, (L i).form.Nondegenerate := by
  classical
  constructor
  · intro h i
    refine (L i).isSymm.isRefl.nondegenerate_iff_separatingLeft.mpr fun v hv ↦ ?_
    have hzero : (Pi.single i v : ∀ i, V i) = 0 :=
      h.1 _ fun y ↦ by rw [pi_form, piForm_single_left]; exact hv (y i)
    simpa using congrFun hzero i
  · intro hL
    exact (pi L).isSymm.isRefl.nondegenerate_iff_separatingLeft.mpr fun _ hx ↦
      eq_zero_of_forall_piForm L hL hx

/-- An orthogonal sum of nondegenerate integral lattices is nondegenerate. -/
instance instIsNondegeneratePi [∀ i, (L i).IsNondegenerate] : (pi L).IsNondegenerate :=
  ⟨(nondegenerate_pi_iff L).mpr fun i ↦ (L i).form_nondegenerate⟩

/-! ## Evenness and positive-definiteness -/

/-- An orthogonal sum is even exactly when every summand is even. -/
@[simp]
theorem isEven_pi_iff : (pi L).IsEven ↔ ∀ i, (L i).IsEven := by
  classical
  simp only [isEven_iff_forall_norm]
  constructor
  · intro h i v
    obtain ⟨z, hz⟩ := h ⟨_, single_mem_pi_carrier L i v.2⟩
    refine ⟨z, ?_⟩
    rw [← hz, norm_pi_apply, Finset.sum_eq_single i (fun j _ hji ↦ by
      simp [Pi.single_eq_of_ne hji]) (by simp)]
    simp
  · intro h x
    choose z hz using fun i ↦ h i ⟨(x : ∀ i, V i) i, (mem_pi_carrier_iff L _).mp x.2 i⟩
    refine ⟨∑ i, z i, ?_⟩
    rw [norm_pi_apply]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hz i

/-- An orthogonal sum of even lattices is even. -/
theorem isEven_pi {L : ∀ i, IntegralLattice (V i)} (hL : ∀ i, (L i).IsEven) : (pi L).IsEven :=
  (isEven_pi_iff L).mpr hL

/-- An orthogonal sum is positive definite exactly when every summand is. -/
@[simp]
theorem isPosDef_pi_iff : (pi L).IsPosDef ↔ ∀ i, (L i).IsPosDef := by
  have h : (pi L).form.toQuadraticMap = QuadraticMap.pi fun i ↦ (L i).form.toQuadraticMap := by
    ext x
    simp
  rw [IsPosDef, h, QuadraticMap.posDef_pi_iff]

/-! ## Rank -/

/-- The rank of an orthogonal sum is the sum of the ranks of its summands. -/
@[simp]
theorem finrank_pi : Module.finrank ℤ (pi L) = ∑ i, Module.finrank ℤ (L i) := by
  have (i : ι) := (L i).finiteDimensional
  simp only [finrank_carrier, Module.finrank_pi_fintype]

/-! ## Isometries

An orthogonal sum is functorial in its summands, and invariant under reindexing the family by an
equivalence of index types.  Reindexing is how a permutation of the components of a reducible root
system acts on the orthogonal sum of their root lattices. -/

namespace Isometry

variable {L}
variable {W : ι → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module ℚ (W i)]
  {M : ∀ i, IntegralLattice (W i)}

/-- The orthogonal sum of a family of integral-lattice isometries, acting coordinatewise. -/
def pi (f : ∀ i, Isometry (L i) (M i)) :
    Isometry (IntegralLattice.pi L) (IntegralLattice.pi M) where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.piCongrRight fun i ↦ (f i : V i ≃ₗ[ℚ] W i)
      map_app' x y := by
        simp only [pi_form, piForm_apply]
        exact Finset.sum_congr rfl fun i _ ↦ (f i).map_app (x i) (y i) }
  map_carrier := by
    ext y
    rw [Submodule.mem_map_equiv, mem_pi_carrier_iff, mem_pi_carrier_iff]
    exact forall_congr' fun i ↦ by
      rw [← (f i).symm.apply_mem_carrier_iff, coe_symm]
      simp only [LinearEquiv.restrictScalars_symm_apply, LinearEquiv.piCongrRight_symm,
        LinearEquiv.piCongrRight_apply]

/-- The orthogonal sum of a family of isometries acts coordinatewise. -/
@[simp]
theorem pi_apply (f : ∀ i, Isometry (L i) (M i)) (x : ∀ i, V i) (i : ι) :
    pi f x i = f i (x i) :=
  (rfl)

/-- The orthogonal sum of identity isometries is the identity of the orthogonal sum. -/
@[simp]
theorem pi_refl : (pi fun i ↦ Isometry.refl (L i)) = Isometry.refl (IntegralLattice.pi L) := by
  ext x i
  simp only [pi_apply, refl_apply]

/-- The inverse of an orthogonal sum of isometries is the orthogonal sum of the inverses. -/
@[simp]
theorem pi_symm (f : ∀ i, Isometry (L i) (M i)) : (pi f).symm = pi fun i ↦ (f i).symm :=
  Isometry.ext fun y ↦ EquivLike.injective (pi f) <| by
    rw [apply_symm_apply]
    ext i
    simp only [pi_apply, apply_symm_apply]

/-- Orthogonal sums of isometries preserve composition coordinatewise. -/
@[simp]
theorem pi_trans {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℚ (X i)]
    {N : ∀ i, IntegralLattice (X i)} (f : ∀ i, Isometry (L i) (M i))
    (g : ∀ i, Isometry (M i) (N i)) :
    (pi f).trans (pi g) = pi fun i ↦ (f i).trans (g i) := by
  ext x i
  simp only [trans_apply, pi_apply]

variable (L)
variable {κ : Type x} [Fintype κ]

/-- **Reindexing an orthogonal sum.**  An equivalence `σ : κ ≃ ι` of index types induces the
isometry from the orthogonal sum of the reindexed family `k ↦ L (σ k)` to the orthogonal sum of
`L`, moving the summand in position `k` to position `σ k`. -/
def piCongrLeft (σ : κ ≃ ι) :
    Isometry (IntegralLattice.pi fun k ↦ L (σ k)) (IntegralLattice.pi L) where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.piCongrLeft ℚ V σ
      map_app' x y := by
        simp only [pi_form, piForm_apply]
        rw [← σ.sum_comp]
        -- `LinearEquiv.piCongrLeft` is `Equiv.piCongrLeft` with its linear structure, and Mathlib
        -- states its evaluation only for the underlying equivalence.
        exact Finset.sum_congr rfl fun k _ ↦ congrArg₂ (fun a b ↦ (L (σ k)).form a b)
          (Equiv.piCongrLeft_apply_apply V σ x k) (Equiv.piCongrLeft_apply_apply V σ y k) }
  map_carrier := by
    ext y
    rw [Submodule.mem_map_equiv, mem_pi_carrier_iff, mem_pi_carrier_iff]
    -- The inverse of `Equiv.piCongrLeft` reads a family at `σ k`.
    exact σ.forall_congr_right (q := fun i ↦ y i ∈ (L i).carrier)

/-- Reindexing an orthogonal sum moves the coordinate in position `k` to position `σ k`. -/
@[simp]
theorem piCongrLeft_apply_apply (σ : κ ≃ ι) (x : ∀ k, V (σ k)) (k : κ) :
    piCongrLeft L σ x (σ k) = x k :=
  Equiv.piCongrLeft_apply_apply V σ x k

/-- The inverse of reindexing an orthogonal sum reads the coordinate in position `k` from
position `σ k`. -/
@[simp]
theorem piCongrLeft_symm_apply (σ : κ ≃ ι) (y : ∀ i, V i) (k : κ) :
    (piCongrLeft L σ).symm y k = y (σ k) := by
  conv_rhs => rw [← apply_symm_apply (piCongrLeft L σ) y]
  exact (piCongrLeft_apply_apply L σ _ k).symm

/-- Reindexing an orthogonal sum along the identity equivalence is the identity. -/
@[simp]
theorem piCongrLeft_refl :
    piCongrLeft L (Equiv.refl ι) = Isometry.refl (IntegralLattice.pi L) := by
  ext x i
  exact (piCongrLeft_apply_apply L (Equiv.refl ι) x i).trans
    (congrFun (refl_apply (IntegralLattice.pi L) x) i).symm

/-- Reindexing commutes with orthogonal sums of isometries: reindexing and then applying `f i` in
each position `i` agrees with applying `f (σ k)` in each position `k` and then reindexing. -/
theorem piCongrLeft_trans_pi (σ : κ ≃ ι) (f : ∀ i, Isometry (L i) (M i)) :
    (piCongrLeft L σ).trans (pi f) = (pi fun k ↦ f (σ k)).trans (piCongrLeft M σ) := by
  ext x i
  obtain ⟨k, rfl⟩ := σ.surjective i
  simp only [trans_apply, pi_apply, piCongrLeft_apply_apply]

end Isometry

end TauCeti.IntegralLattice
