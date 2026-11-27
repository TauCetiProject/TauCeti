/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Gram
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import TauCeti.NumberTheory.GeometryOfNumbers.PosDefForm.Basic

/-!
# Gram forms of positive definite integral lattices

The Gram matrix of an integral basis gives a positive definite real form. These Gram forms
are exactly the integral points of the positive cone. Changing the basis by a unimodular matrix
`U` acts on the form by `A ↦ UᵀAU`, so the orbit of the form depends only on the lattice.
Two lattices are isometric precisely when their Gram forms belong to the same orbit.

`IntegralLattice.gramFormClass` records this orbit without choosing a basis in its interface.
`PosDefForm.descend` evaluates an invariant of forms on a lattice of the corresponding rank.
The comparison uses `IntegralLattice.isPosDef_iff_posDef_map_gramMatrix` to recognize the real
positive cone and `IntegralLattice.Isometry.ofGramMatrixEq` to recover a lattice isometry.
-/

public section

open Module Matrix

namespace TauCeti

variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V} {M : IntegralLattice W}

namespace IntegralLattice

/-- The positive definite real form of an integral lattice in the basis `b`. -/
noncomputable def gramForm (hL : L.IsPosDef) (b : Basis (Fin n) ℤ L) : PosDefForm n :=
  ⟨(L.gramMatrix b).map (Int.cast : ℤ → ℝ), (L.isPosDef_iff_posDef_map_gramMatrix b).mp hL⟩

/-- The matrix of the Gram form is the entrywise real cast of the integral Gram matrix. -/
@[simp] theorem coe_gramForm (hL : L.IsPosDef) (b : Basis (Fin n) ℤ L) :
    (gramForm hL b).val = (L.gramMatrix b).map (Int.cast : ℤ → ℝ) :=
  (rfl)

/-- A lattice Gram form has integer entries in every integral basis. -/
@[simp] theorem isIntegralForm_gramForm (hL : L.IsPosDef) (b : Basis (Fin n) ℤ L) :
    (gramForm hL b).IsIntegralForm :=
  PosDefForm.isIntegralForm_iff_exists_matrix.mpr ⟨_, (coe_gramForm hL b).symm⟩

/-- Pairing the coordinates of two lattice vectors gives their integral pairing cast to `ℝ`. -/
@[simp] theorem pairing_gramForm_repr (hL : L.IsPosDef) (b : Basis (Fin n) ℤ L) (x y : L) :
    (gramForm hL b).pairing (fun i ↦ (b.repr x i : ℝ)) (fun i ↦ (b.repr y i : ℝ)) =
      (L.integralForm x y : ℝ) := by
  rw [PosDefForm.pairing_apply, coe_gramForm, L.gramMatrix_eq_toMatrix,
    L.integralForm.apply_eq_dotProduct_toMatrix_mulVec b x y]
  simp [dotProduct, Matrix.mulVec]

/-- Evaluating the Gram form on the coordinates of a lattice vector gives its squared norm. -/
@[simp] theorem eval_gramForm_repr (hL : L.IsPosDef) (b : Basis (Fin n) ℤ L) (x : L) :
    (gramForm hL b).eval (fun i ↦ (b.repr x i : ℝ)) = (L.integralNorm x : ℝ) := by
  rw [← PosDefForm.pairing_self, pairing_gramForm_repr, integralNorm_apply]

/-- Changing an integral basis by an automorphism acts on the Gram form by the
unimodular matrix of the automorphism in the original basis. -/
theorem gramForm_map (hL : L.IsPosDef) (b : Basis (Fin n) ℤ L) (e : L ≃ₗ[ℤ] L) :
    gramForm hL (b.map e) = PosDefForm.actGL (b.toGL e) (gramForm hL b) := by
  have hmat : (b.toGL e : Matrix (Fin n) (Fin n) ℤ) = b.toMatrix (b.map e) := by
    simp only [Basis.coe_toGL, LinearMap.toMatrix_eq_basisToMatrix, Basis.coe_map,
      LinearEquiv.coe_coe]
  apply Subtype.ext
  simp only [PosDefForm.coe_actGL, hmat, coe_gramForm, L.gramMatrix_eq_toMatrix,
    ← Int.coe_castRingHom, ← Matrix.transpose_map, ← Matrix.map_mul,
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix]

/-- The Gram form in `b'` is obtained by congruence with the matrix whose columns are the
coordinates of `b'` in `b`. -/
theorem gramForm_eq_actGL (hL : L.IsPosDef) (b b' : Basis (Fin n) ℤ L) :
    gramForm hL b' =
      PosDefForm.actGL (b.toGL (b.equiv b' (Equiv.refl _))) (gramForm hL b) := by
  simpa only [Basis.map_equiv, Equiv.refl_symm, Basis.reindex_refl] using
    gramForm_map hL b (b.equiv b' (Equiv.refl _))

/-- Transporting a basis by a lattice isometry leaves its Gram form unchanged. -/
@[simp] theorem Isometry.gramForm_map (e : Isometry L M) (hL : L.IsPosDef)
    (b : Basis (Fin n) ℤ L) :
    gramForm (e.isPosDef_iff.mp hL) (b.map e.carrierEquiv) = gramForm hL b := by
  apply Subtype.ext
  simp only [coe_gramForm, ← e.carrierBasisEquiv_apply, e.gramMatrix_carrierBasisEquiv]

/-- Two positive definite integral lattices are isometric precisely when their Gram forms
in the given bases are integrally congruent. -/
theorem nonempty_isometry_iff_exists_gramForm_eq_actGL (hL : L.IsPosDef) (hM : M.IsPosDef)
    (b : Basis (Fin n) ℤ L) (c : Basis (Fin n) ℤ M) :
    Nonempty (Isometry L M) ↔
      ∃ U : GL (Fin n) ℤ, gramForm hM c = PosDefForm.actGL U (gramForm hL b) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨_, (gramForm_eq_actGL hM (b.map e.carrierEquiv) c).trans
      (congrArg _ (e.gramForm_map hL b))⟩
  · rintro ⟨U, hU⟩
    obtain ⟨f, rfl⟩ := b.toGL.surjective U
    rw [← gramForm_map] at hU
    refine ⟨Isometry.ofGramMatrixEq (b.map f) c (Matrix.map_injective
      (Int.cast_injective (α := ℝ)) ?_)⟩
    simpa only [coe_gramForm] using congrArg Subtype.val hU.symm

/-- The congruence class of the Gram form of a positive definite lattice of rank `n`. -/
noncomputable def gramFormClass (hL : L.IsPosDef) (hn : finrank ℤ L = n) :
    MulAction.orbitRel.Quotient (GL (Fin n) ℤ)ᵐᵒᵖ (PosDefForm n) :=
  ⟦gramForm hL (finBasisOfFinrankEq ℤ L hn)⟧

/-- Every integral basis gives a representative of the lattice's Gram-form class. -/
theorem gramFormClass_eq (hL : L.IsPosDef) (hn : finrank ℤ L = n) (b : Basis (Fin n) ℤ L) :
    gramFormClass hL hn = ⟦gramForm hL b⟧ := by
  apply Quotient.sound
  exact ⟨MulOpposite.op _, (gramForm_eq_actGL hL b _).symm⟩

/-- The Gram-form class is a complete isometry invariant for positive definite lattices. -/
theorem gramFormClass_eq_iff (hL : L.IsPosDef) (hM : M.IsPosDef)
    (hnL : finrank ℤ L = n) (hnM : finrank ℤ M = n) :
    gramFormClass hL hnL = gramFormClass hM hnM ↔ Nonempty (Isometry L M) := by
  let b := finBasisOfFinrankEq ℤ L hnL
  let c := finBasisOfFinrankEq ℤ M hnM
  rw [eq_comm, gramFormClass_eq hL hnL b, gramFormClass_eq hM hnM c, Quotient.eq,
    nonempty_isometry_iff_exists_gramForm_eq_actGL hL hM b c]
  exact ⟨fun ⟨U, hU⟩ ↦ ⟨U.unop, hU.symm⟩, fun ⟨U, hU⟩ ↦ ⟨MulOpposite.op U, hU.symm⟩⟩

end IntegralLattice

namespace PosDefForm

open IntegralLattice

/-- In a rational space with an `n`-element basis, the lattice Gram forms are exactly the
integral positive definite forms of rank `n`. -/
theorem isIntegralForm_iff_exists_gramForm (A : PosDefForm n) (bV : Basis (Fin n) ℚ V) :
    A.IsIntegralForm ↔ ∃ (L : IntegralLattice V) (hL : L.IsPosDef)
      (b : Basis (Fin n) ℤ L), gramForm hL b = A := by
  constructor
  · rw [isIntegralForm_iff_exists_matrix]
    rintro ⟨G, hG⟩
    have hs : G.IsSymm := (Matrix.isSymm_map_iff (Int.cast_injective (α := ℝ))).mp
      (hG ▸ A.property.isHermitian.isSymm)
    let c := ofGramMatrix.basis bV G hs
    have hp : (ofGramMatrix bV G hs).IsPosDef := by
      rw [isPosDef_iff_posDef_map_gramMatrix (K := ℝ) _ c]
      simpa only [c, gramMatrix_ofGramMatrix, hG] using A.property
    exact ⟨_, hp, c, Subtype.ext (by simpa only [coe_gramForm, c, gramMatrix_ofGramMatrix]
      using hG)⟩
  · rintro ⟨L, hL, b, rfl⟩
    exact isIntegralForm_gramForm hL b

variable {X : Sort*} (f : PosDefForm n → X)
variable (hf : ∀ (U : GL (Fin n) ℤ) (A : PosDefForm n), f (actGL U A) = f A)

/-- The value on a rank-`n` lattice of a function invariant under integral congruence. -/
noncomputable def descend (hL : L.IsPosDef) (hn : finrank ℤ L = n) : X :=
  (gramFormClass hL hn).liftOn f (by
    rintro A B ⟨U, hU⟩
    exact (congrArg f hU.symm).trans (hf U.unop B))

/-- The descended invariant can be evaluated in any integral basis. -/
theorem descend_eq (hL : L.IsPosDef) (hn : finrank ℤ L = n) (b : Basis (Fin n) ℤ L) :
    descend f hf hL hn = f (gramForm hL b) := by
  rw [descend, gramFormClass_eq hL hn b]
  rfl

/-- Isometric lattices have the same value of every descended invariant of Gram forms. -/
theorem _root_.TauCeti.IntegralLattice.Isometry.descend_eq (e : Isometry L M) (hL : L.IsPosDef)
    (hn : finrank ℤ L = n) :
    descend f hf hL hn =
      descend f hf (e.isPosDef_iff.mp hL) (e.carrierEquiv.finrank_eq.symm.trans hn) := by
  unfold descend
  rw [(gramFormClass_eq_iff hL (e.isPosDef_iff.mp hL) hn _).mpr ⟨e⟩]

end PosDefForm

end TauCeti
