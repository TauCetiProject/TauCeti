/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Lattice

import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Cartan data from realizations

A rational realization of a symmetrizable generalized Cartan matrix `A`, together with a coweight
lattice `Y` in it, is a Cartan datum: the coweight lattice and its weight lattice `P` are in perfect
duality, they contain the simple coroots and roots, these stay linearly independent over `ℤ`, and
`⟨αⱼ, hᵢ⟩ = aᵢⱼ`. This file records that datum, compares data coming from nested coweight
lattices, and proves that every Cartan datum on a free coweight lattice of finite rank arises in
this way.

The comparison lets the theory of realizations (roots and coroots in a rational vector space, the
Weyl group acting on it) be read on the full lattices of a Cartan datum, and conversely: the data
attached to a realization keep its Cartan matrix, roots, coroots, pairing and reflections.

## Main definitions

* `TauCeti.CartanRealization.CoweightLattice.toCartanDatum`: the Cartan datum
  `(P, L, αᵢ, hᵢ)` of a coweight lattice `L` of a rational realization, for a chosen symmetrizer.
* `TauCeti.CartanRealization.CoweightLattice.homOfLE`: the morphism of Cartan data induced by an
  inclusion of coweight lattices of the same realization.
* `TauCeti.CartanDatum.realization`: the rational realization of the Cartan matrix of a datum on
  `ℚ^κ`, through a `ℤ`-basis of the coweight lattice indexed by `κ`.
* `TauCeti.CartanDatum.coweightLattice`: the image of the coweight lattice in it.
* `TauCeti.CartanDatum.realizationHom`: the morphism from a datum to the datum of its realization.

## Main results

* `TauCeti.CartanRealization.CoweightLattice.cartan_toCartanDatum`: the Cartan matrix of the
  datum of a coweight lattice is the matrix that was realized.
* `TauCeti.CartanRealization.CoweightLattice.coe_coreflection_toCartanDatum`: its simple
  coreflections are the restrictions of the reflections `y ↦ y − αᵢ(y) hᵢ` of the realization.
* `TauCeti.CartanRealization.CoweightLattice.coe_weightMap_homOfLE`: the induced map of weight
  lattices is the inclusion of functionals.
* `TauCeti.CartanDatum.mem_coweightLattice_iff`: the coweight lattice of the realization of a datum
  consists of the coordinate vectors of its coweights.
* `TauCeti.CartanDatum.realizationHom_toLinearMap_bijective`: every Cartan datum whose coweight
  lattice has a finite basis is isomorphic to the datum of a coweight lattice of a rational
  realization of its Cartan matrix, with inverse `TauCeti.CartanDatum.Hom.inverse`.
* `TauCeti.CartanDatum.realizationHom_weightMap_bijective`: this isomorphism is also bijective on
  weights.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1 (realizations) and §10.1
  (the lattice of integral weights).
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.1 (Cartan data) and §2.2 (root data).
-/

public section

open Module

namespace TauCeti

namespace CartanRealization

namespace CoweightLattice

variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {A : Matrix I I ℤ}
  {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H} (L : R.CoweightLattice)
  (d : I → ℕ) (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hd : ∀ i, 0 < d i)
  (hsymm : ∀ i j, (d i : ℤ) * A i j = d j * A j i)

/-- The **Cartan datum of a coweight lattice** `L` of a rational realization of a symmetrizable
generalized Cartan matrix `A` (diagonal `2`, nonpositive off-diagonal entries, symmetrizer `d`):
the weight lattice `P` and the coweight lattice `L` with the evaluation pairing, the simple roots
`αᵢ ∈ P` and the simple coroots `hᵢ ∈ L`, and the symmetrizer `d`. -/
noncomputable def toCartanDatum : CartanDatum I L.weightLattice L.lattice where
  pairing := L.pairing
  root := L.root
  coroot := L.coroot
  linearIndependent_root := L.linearIndependent_root
  linearIndependent_coroot := L.linearIndependent_coroot
  pairing_root_coroot_self i := by rw [pairing_root_coroot, hdiag]
  pairing_root_coroot_nonpos {i j} hij := by
    rw [pairing_root_coroot]
    exact hoff i j hij
  symmetrizer := d
  symmetrizer_pos := hd
  symmetrizer_mul_pairing i j := by
    rw [pairing_root_coroot, pairing_root_coroot]
    exact hsymm i j

-- `(rfl)`, not `rfl`: the body of `toCartanDatum` is not exposed, and the parenthesised form
-- keeps these proofs out of the exported definitional-equality check.
@[simp]
theorem toCartanDatum_pairing : (L.toCartanDatum d hdiag hoff hd hsymm).pairing = L.pairing :=
  (rfl)

@[simp]
theorem toCartanDatum_root : (L.toCartanDatum d hdiag hoff hd hsymm).root = L.root := (rfl)

@[simp]
theorem toCartanDatum_coroot : (L.toCartanDatum d hdiag hoff hd hsymm).coroot = L.coroot := (rfl)

@[simp]
theorem toCartanDatum_symmetrizer : (L.toCartanDatum d hdiag hoff hd hsymm).symmetrizer = d :=
  (rfl)

/-- The Cartan matrix of the datum of a coweight lattice is the realized matrix. -/
@[simp]
theorem cartan_toCartanDatum : (L.toCartanDatum d hdiag hoff hd hsymm).cartan = A := by
  ext i j
  simp [CartanDatum.cartan_apply]

/-- The simple coreflections of the datum of a coweight lattice are the restrictions of the
reflections `y ↦ y − αᵢ(y) hᵢ` of the realization. -/
@[simp]
theorem coe_coreflection_toCartanDatum (i : I) (y : L.lattice) :
    (((L.toCartanDatum d hdiag hoff hd hsymm).coreflection i y : L.lattice) : H) =
      y - R.root i y • R.coroot i := by
  simp [CartanDatum.coreflection_apply, ← Int.cast_smul_eq_zsmul ℚ]

/-- The simple reflections of the datum of a coweight lattice are the restrictions of the
reflections `φ ↦ φ − φ(hᵢ) αᵢ` of the dual of the realization. -/
@[simp]
theorem coe_reflection_toCartanDatum (i : I) (φ : L.weightLattice) :
    (((L.toCartanDatum d hdiag hoff hd hsymm).reflection i φ : L.weightLattice) : Dual ℚ H) =
      φ - (φ : Dual ℚ H) (R.coroot i) • R.root i := by
  simp [CartanDatum.reflection_apply, ← Int.cast_smul_eq_zsmul ℚ]

/-! The simp lemmas above rewrite the roots, coroots and pairing of `L.toCartanDatum` to those of
`L`, so the general simp lemmas about `TauCeti.CartanDatum` stated with `D.root` and `D.coroot`
no longer apply to them. The following lemmas restate those general lemmas in this normal form. -/

@[simp]
theorem coreflection_toCartanDatum_coroot_self (i : I) :
    (L.toCartanDatum d hdiag hoff hd hsymm).coreflection i (L.coroot i) = -L.coroot i :=
  (L.toCartanDatum d hdiag hoff hd hsymm).coreflection_coroot_self i

@[simp]
theorem reflection_toCartanDatum_root_self (i : I) :
    (L.toCartanDatum d hdiag hoff hd hsymm).reflection i (L.root i) = -L.root i :=
  (L.toCartanDatum d hdiag hoff hd hsymm).reflection_root_self i

section Hom

variable {L d hdiag hoff hd hsymm} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {D : CartanDatum I X Y}

@[simp]
theorem toLinearMap_coroot (f : CartanDatum.Hom (L.toCartanDatum d hdiag hoff hd hsymm) D)
    (i : I) : f.toLinearMap (L.coroot i) = D.coroot i :=
  f.map_coroot i

@[simp]
theorem pairing_weightMap (f : CartanDatum.Hom (L.toCartanDatum d hdiag hoff hd hsymm) D) (x : X)
    (y : L.lattice) : L.pairing (f.weightMap x) y = D.pairing x (f.toLinearMap y) :=
  f.pairing_weightMap x y

@[simp]
theorem pairing_root_toLinearMap (f : CartanDatum.Hom D (L.toCartanDatum d hdiag hoff hd hsymm))
    (i : I) (y : Y) : L.pairing (L.root i) (f.toLinearMap y) = D.pairing (D.root i) y :=
  f.pairing_root_map i y

@[simp]
theorem weightMap_root (f : CartanDatum.Hom D (L.toCartanDatum d hdiag hoff hd hsymm)) (i : I) :
    f.weightMap (L.root i) = D.root i :=
  f.weightMap_root i

end Hom

/-! ### Nested coweight lattices -/

/-- The **morphism of Cartan data induced by an inclusion** `L ⊆ L'` of coweight lattices of the
same realization, such as `ℤ h ⊆ ℤ (h / 2)` in type `A₁`: the inclusion of coweight lattices. Its
transpose `TauCeti.CartanDatum.Hom.weightMap` is the inclusion of the weight lattices, which
reverses the inclusion (`TauCeti.CartanRealization.CoweightLattice.coe_weightMap_homOfLE`). -/
noncomputable def homOfLE {L L' : R.CoweightLattice} (h : L.lattice ≤ L'.lattice) :
    CartanDatum.Hom (L.toCartanDatum d hdiag hoff hd hsymm)
      (L'.toCartanDatum d hdiag hoff hd hsymm) where
  toLinearMap := Submodule.inclusion h
  map_coroot _ := by ext; simp
  pairing_root_map i y := Int.cast_injective (α := ℚ) <| by
    simp only [toCartanDatum_pairing, toCartanDatum_root, cast_pairing, coe_root,
      Submodule.coe_inclusion]
  symmetrizer_eq := rfl

@[simp]
theorem homOfLE_toLinearMap {L L' : R.CoweightLattice} (h : L.lattice ≤ L'.lattice) :
    (homOfLE d hdiag hoff hd hsymm h).toLinearMap = Submodule.inclusion h := (rfl)

/-- The transpose of the morphism induced by an inclusion of coweight lattices is the inclusion of
the weight lattices: it does not change the underlying functional. -/
@[simp]
theorem coe_weightMap_homOfLE {L L' : R.CoweightLattice} (h : L.lattice ≤ L'.lattice)
    (φ : L'.weightLattice) :
    ((homOfLE d hdiag hoff hd hsymm h).weightMap φ : Dual ℚ H) = φ := by
  have hle : L'.weightLattice ≤ L.weightLattice := by
    rw [weightLattice_def, weightLattice_def]
    exact Submodule.dualLattice_antitone ℚ h
  rw [← (homOfLE d hdiag hoff hd hsymm h).eq_weightMap (g := Submodule.inclusion hle)
    fun φ y ↦ Int.cast_injective (α := ℚ) (by simp)]
  simp

@[simp]
theorem homOfLE_refl : homOfLE d hdiag hoff hd hsymm (le_refl L.lattice) = .id _ := by
  ext
  simp

@[simp]
theorem homOfLE_comp_homOfLE {L L' L'' : R.CoweightLattice} (h : L.lattice ≤ L'.lattice)
    (h' : L'.lattice ≤ L''.lattice) :
    (homOfLE d hdiag hoff hd hsymm h').comp (homOfLE d hdiag hoff hd hsymm h) =
      homOfLE d hdiag hoff hd hsymm (h.trans h') := by
  ext
  simp

end CoweightLattice

end CartanRealization

namespace CartanDatum

/-! ### Every Cartan datum comes from a realization -/

variable {ι X Y κ : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)
  (b : Basis κ ℤ Y)

/-- The pairing of a simple root with a coweight, computed in coordinates. -/
private theorem sum_repr_mul_pairing_root [Fintype κ] (j : ι) (y : Y) :
    ∑ k, (b.repr y k : ℚ) * D.pairing (D.root j) (b k) = D.pairing (D.root j) y := by
  conv_rhs => rw [← b.sum_repr y]
  push_cast [map_sum, map_zsmul]
  simp

variable [Finite κ]

/-- The simple coroots of a datum stay independent over `ℚ` in coordinates. -/
private theorem linearIndependent_repr_coroot :
    LinearIndependent ℚ fun i k ↦ (b.repr (D.coroot i) k : ℚ) := by
  simpa [Function.comp_def] using (linearIndependent_algebraMap_comp_iff (S := ℚ)).mpr
    (D.linearIndependent_coroot.map' b.equivFun.toLinearMap b.equivFun.ker)

/-- The values `(⟨αⱼ, bₖ⟩)ₖ` of the simple roots of a datum on a basis stay independent over `ℚ`. -/
private theorem linearIndependent_pairing_root_basis :
    LinearIndependent ℚ fun j k ↦ (D.pairing (D.root j) (b k) : ℚ) := by
  let e := D.pairing.toPerfPair.trans (b.constr ℤ).symm
  simpa [e, Function.comp_def] using (linearIndependent_algebraMap_comp_iff (S := ℚ)).mpr
    (D.linearIndependent_root.map' e.toLinearMap e.ker)

/-- The **rational realization of the Cartan matrix of a datum** on `ℚ^κ`, through a `ℤ`-basis `b`
of the coweight lattice: the simple coroot `hᵢ` is its coordinate vector `(bₖ*(hᵢ))ₖ`, and the
simple root `αⱼ` is the functional `x ↦ Σₖ xₖ ⟨αⱼ, bₖ⟩`. -/
noncomputable def realization : CartanRealization (D.cartan.map (Int.cast : ℤ → ℚ)) (κ → ℚ) where
  coroot i k := b.repr (D.coroot i) k
  root j := (Pi.basisFun ℚ κ).constr ℚ fun k ↦ (D.pairing (D.root j) (b k) : ℚ)
  coroot_linearIndependent := linearIndependent_repr_coroot D b
  root_linearIndependent :=
    (linearIndependent_pairing_root_basis D b).map' _ ((Pi.basisFun ℚ κ).constr ℚ).ker
  root_coroot i j := by
    have := Fintype.ofFinite κ
    rw [Basis.constr_apply_fintype, Matrix.map_apply, cartan_apply,
      ← sum_repr_mul_pairing_root D b]
    simp [mul_comm]

@[simp]
theorem realization_coroot (i : ι) :
    (D.realization b).coroot i = fun k ↦ (b.repr (D.coroot i) k : ℚ) := (rfl)

theorem realization_root_apply [Fintype κ] (j : ι) (x : κ → ℚ) :
    (D.realization b).root j x = ∑ k, x k * D.pairing (D.root j) (b k) := by
  simp [realization, Basis.constr_apply_fintype]

/-- The simple root `αⱼ` of the realization takes the value `⟨αⱼ, y⟩` on the coordinate vector of
a coweight `y`. -/
@[simp]
theorem realization_root_apply_repr (j : ι) (y : Y) :
    (D.realization b).root j (fun k ↦ (b.repr y k : ℚ)) = D.pairing (D.root j) y := by
  have := Fintype.ofFinite κ
  simp [realization_root_apply, sum_repr_mul_pairing_root]

/-- The coweight lattice of a datum inside its realization: the integral vectors of `ℚ^κ`, which
are the coordinate vectors of the coweights (`TauCeti.CartanDatum.mem_coweightLattice_iff`). -/
noncomputable def coweightLattice : (D.realization b).CoweightLattice :=
  .ofBasis (Pi.basisFun ℚ κ)
    (fun i ↦ by simp [realization_coroot, Basis.mem_span_iff_repr_mem])
    fun j k ↦ ⟨D.pairing (D.root j) (b k), by
      classical
      have := Fintype.ofFinite κ
      simp [realization_root_apply, Pi.single_apply]⟩

theorem coweightLattice_lattice :
    (D.coweightLattice b).lattice = Submodule.span ℤ (Set.range (Pi.basisFun ℚ κ)) := by
  rw [coweightLattice]
  exact CartanRealization.CoweightLattice.lattice_ofBasis _ _ _

/-- The coweight lattice of the realization of a datum consists of the coordinate vectors of the
coweights. -/
theorem mem_coweightLattice_iff {x : κ → ℚ} :
    x ∈ (D.coweightLattice b).lattice ↔ ∃ y : Y, (fun k ↦ (b.repr y k : ℚ)) = x := by
  rw [coweightLattice_lattice, Basis.mem_span_iff_repr_mem]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · choose n hn using hx
    refine ⟨b.equivFun.symm n, funext fun k ↦ ?_⟩
    rw [← b.equivFun_apply, b.equivFun.apply_symm_apply]
    simpa using hn k
  · rintro ⟨y, rfl⟩ k
    simp

/-- The **morphism from a Cartan datum to the datum of its realization**: a coweight goes to its
coordinate vector. It is bijective on coweights
(`TauCeti.CartanDatum.realizationHom_toLinearMap_bijective`) and on weights
(`TauCeti.CartanDatum.realizationHom_weightMap_bijective`), so it is an isomorphism, with inverse
`TauCeti.CartanDatum.Hom.inverse`. -/
noncomputable def realizationHom :
    Hom D ((D.coweightLattice b).toCartanDatum D.symmetrizer D.cartan_apply_self
      (fun _ _ ↦ D.cartan_nonpos) D.symmetrizer_pos D.symmetrizer_mul_cartan) where
  toLinearMap := LinearMap.codRestrict _ (Pi.algebraMap κ ℤ ℚ ∘ₗ b.equivFun.toLinearMap)
    fun y ↦ (D.mem_coweightLattice_iff b).mpr ⟨y, by ext; simp [Pi.algebraMap]⟩
  map_coroot i := by
    ext
    simp [realization_coroot, Pi.algebraMap]
  pairing_root_map i y := Int.cast_injective (α := ℚ) <| by
    simp [Pi.algebraMap, Function.comp_def]
  symmetrizer_eq := rfl

@[simp]
theorem coe_realizationHom_toLinearMap (y : Y) :
    ((D.realizationHom b).toLinearMap y : κ → ℚ) = fun k ↦ (b.repr y k : ℚ) := by
  ext
  simp [realizationHom, Pi.algebraMap]

/-- **Every Cartan datum on a coweight lattice with a finite basis comes from a realization**: the
coordinates in a basis are a bijection from its coweight lattice onto the coweight lattice of the
datum of a rational realization of its Cartan matrix. Since `TauCeti.CartanDatum.realizationHom`
is a morphism of Cartan data, this makes it an isomorphism, with inverse
`TauCeti.CartanDatum.Hom.inverse`. -/
theorem realizationHom_toLinearMap_bijective :
    Function.Bijective (D.realizationHom b).toLinearMap := by
  refine ⟨fun y z h ↦ b.repr.injective <| Finsupp.ext fun k ↦ ?_, fun x ↦ ?_⟩
  · simpa using congr_fun (congrArg Subtype.val h) k
  · obtain ⟨y, hy⟩ := (D.mem_coweightLattice_iff b).mp x.property
    exact ⟨y, Subtype.ext (by simpa using hy)⟩

/-- The morphism from a Cartan datum to the datum of its realization is bijective on weights. -/
theorem realizationHom_weightMap_bijective : Function.Bijective (D.realizationHom b).weightMap :=
  (D.realizationHom b).weightMap_bijective (D.realizationHom_toLinearMap_bijective b)

end CartanDatum

end TauCeti
