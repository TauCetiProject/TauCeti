/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
public import TauCeti.Analysis.Matrix.UnitaryGroup.Kostant
public import TauCeti.RepresentationTheory.OrbitSpace
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The coadjoint orbit space of `U(n)` is the closed Weyl chamber

Through the trace pairing `⟨H, X⟩ = -i tr(H X)`, the dual `𝔲(n)*` of the Lie algebra of
`U(n) = Matrix.unitaryGroup ι ℂ` is the space of Hermitian matrices
(`TauCeti.unitaryTracePairingEquiv`), and the coadjoint action is unitary conjugation
`H ↦ U H Uᴴ` (`TauCeti.unitaryCoadjointRepresentation_unitaryTracePairing`). This file computes the
orbit space of this action: a coadjoint orbit is determined by the eigenvalues of `H`, listed in
decreasing order, and every decreasing list occurs. In the coordinates of the diagonal torus, the
decreasing lists form the closed positive Weyl chamber of `𝔱* = ℝⁿ`, and the chamber is a
fundamental domain for the coadjoint action.

We write `unitaryConjRepresentation ι` for the conjugation representation of `U(n)` on the
Hermitian matrices, which the trace pairing intertwines with the coadjoint representation
(`TauCeti.unitaryTracePairing_unitaryConjRepresentation`). Its orbit space
`Quotient (unitaryConjRepresentation ι).orbitRel` carries the quotient topology, and it is
Hausdorff since `U(n)` is compact. The topology is stated in this Hermitian model because
`Module.Dual` carries no topology.

* The decreasing eigenvalue list `Matrix.IsHermitian.eigenvalues₀` is constant on orbits, since
  unitary conjugation preserves the characteristic polynomial, which determines it
  (`Matrix.IsHermitian.eigenvalues₀_mul_mul_star`).
* Two Hermitian matrices with the same eigenvalue list are unitarily conjugate, by the spectral
  theorem (`TauCeti.unitaryConjRepresentation_orbitRel_iff`).
* A decreasing list `s` is the eigenvalue list of the real diagonal matrix `diag(s)`
  (`TauCeti.eigenvalues₀_unitaryChamberDiagonal`).

Hence the eigenvalue list is a homeomorphism from the orbit space onto the closed chamber
`{s : Fin n → ℝ // Antitone s}` (`TauCeti.unitaryConjOrbitHomeomorph`). It is continuous because
the decreasing eigenvalues depend continuously on the matrix (`Matrix.continuous_eigenvalues₀`),
and its inverse `s ↦ [diag(s)]` is continuous, so no properness argument is needed. Read through
the trace pairing, this is the bijection between coadjoint orbits and the chamber
(`TauCeti.unitaryCoadjointOrbitEquiv`), whose inverse sends `s` to the orbit of the torus-fixed
covector `⟨diag(s), ·⟩` (`TauCeti.unitaryCoadjointOrbitEquiv_symm_apply`). Equivalently, every
coadjoint orbit contains `⟨diag(s), ·⟩` for exactly one decreasing `s`
(`TauCeti.existsUnique_antitone_orbitRel_unitaryTorusDualInclusion`).

The center of `𝔲(n)` is the line of scalar matrices, dual to the line of constant lists in `𝔱*`.
The chamber is invariant under adding a constant list, so it is the product of this central line
with the decreasing lists of sum zero, the closed chamber of `𝔰𝔲(n)`.

## Main definitions

* `TauCeti.unitaryConjRepresentation ι`: the conjugation representation `H ↦ U H Uᴴ` of `U(n)` on
  the Hermitian matrices.
* `TauCeti.unitaryConjOrbitHomeomorph ι`: the homeomorphism from its orbit space onto the closed
  chamber of decreasing eigenvalue lists.
* `TauCeti.unitaryCoadjointOrbitEquiv ι`: the bijection from the coadjoint orbit space of `U(n)`
  onto the closed chamber.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV (conjugacy classes and Weyl chambers).
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 4.1.5 (the spectral theorem for Hermitian matrices).
-/

public section

noncomputable section

open Matrix Module Complex

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Unitary conjugation of Hermitian matrices -/

variable (ι) in
/-- The **conjugation representation** of `U(n)` on the Hermitian matrices, `H ↦ U H Uᴴ`. The trace
pairing identifies it with the coadjoint representation
(`TauCeti.unitaryTracePairing_unitaryConjRepresentation`). -/
def unitaryConjRepresentation :
    Representation ℝ (unitaryGroup ι ℂ) (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) where
  toFun U :=
    { toFun H := ⟨U * H * star (U : Matrix ι ι ℂ),
        (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).conjugate _⟩
      map_add' H K := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
      map_smul' c H := Subtype.ext (by simp) }
  map_one' := by ext H : 2; simp
  map_mul' U V := by ext H : 2; simp [Matrix.mul_assoc]

@[simp]
theorem coe_unitaryConjRepresentation_apply (U : unitaryGroup ι ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    (unitaryConjRepresentation ι U H : Matrix ι ι ℂ) = U * H * star (U : Matrix ι ι ℂ) :=
  (rfl)

/-- **The trace pairing intertwines conjugation with the coadjoint action**:
`⟨U H Uᴴ, ·⟩ = Ad*_U ⟨H, ·⟩`. -/
theorem unitaryTracePairing_unitaryConjRepresentation (U : unitaryGroup ι ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    unitaryTracePairing ι (unitaryConjRepresentation ι U H) =
      unitaryCoadjointRepresentation ι U (unitaryTracePairing ι H) :=
  (unitaryCoadjointRepresentation_unitaryTracePairing U H).symm

/-- The conjugation action `(U, H) ↦ U H Uᴴ` is jointly continuous. -/
theorem continuous_unitaryConjRepresentation :
    Continuous fun p : unitaryGroup ι ℂ × selfAdjoint.submodule ℝ (Matrix ι ι ℂ) ↦
      unitaryConjRepresentation ι p.1 p.2 :=
  Continuous.subtype_mk (by fun_prop) _

/-- The orbit space of the conjugation action is Hausdorff. -/
instance : T2Space (Quotient (unitaryConjRepresentation ι).orbitRel) :=
  Representation.t2Space_quotient_orbitRel _ continuous_unitaryConjRepresentation

/-! ### Eigenvalue lists classify the orbits -/

/-- The decreasing eigenvalue list of an element of `selfAdjoint.submodule ℝ (Matrix ι ι ℂ)`. -/
abbrev hermitianEigenvalues₀ (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    Fin (Fintype.card ι) → ℝ :=
  (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).isHermitian.eigenvalues₀

/-- The decreasing eigenvalue list is constant on the orbits of the conjugation action. -/
@[simp]
theorem hermitianEigenvalues₀_unitaryConjRepresentation (U : unitaryGroup ι ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    hermitianEigenvalues₀ (unitaryConjRepresentation ι U H) = hermitianEigenvalues₀ H :=
  IsHermitian.eigenvalues₀_mul_mul_star _ U.property _

/-- **Hermitian matrices are unitarily conjugate exactly when they have the same eigenvalues.** -/
theorem unitaryConjRepresentation_orbitRel_iff {H K : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)} :
    (unitaryConjRepresentation ι).orbitRel H K ↔
      hermitianEigenvalues₀ H = hermitianEigenvalues₀ K := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨U, hU⟩ := (Representation.orbitRel_apply _).mp h
    exact hU ▸ hermitianEigenvalues₀_unitaryConjRepresentation U K
  set hH := (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).isHermitian
  set hK := (K.property : IsSelfAdjoint (K : Matrix ι ι ℂ)).isHermitian
  -- Both are conjugate to the same real diagonal matrix by the spectral theorem.
  have he : hH.eigenvalues = hK.eigenvalues := by
    funext i
    simp only [IsHermitian.eigenvalues]
    exact congrFun h _
  -- Both are conjugate to the same real diagonal matrix `D` by the spectral theorem.
  obtain ⟨D, V, W, hV, hW⟩ : ∃ (D : Matrix ι ι ℂ) (V W : unitaryGroup ι ℂ),
      (H : Matrix ι ι ℂ) = V * D * star (V : Matrix ι ι ℂ) ∧
        (K : Matrix ι ι ℂ) = W * D * star (W : Matrix ι ι ℂ) :=
    ⟨_, hH.eigenvectorUnitary, hK.eigenvectorUnitary, by simpa [he] using hH.spectral_theorem,
      by simpa using hK.spectral_theorem⟩
  refine (Representation.orbitRel_apply _).mpr ⟨V * star W, Subtype.ext ?_⟩
  have hu : star (W : Matrix ι ι ℂ) * W = 1 := Unitary.star_mul_self_of_mem W.property
  rw [coe_unitaryConjRepresentation_apply, hV, hW]
  simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star]
  calc (V : Matrix ι ι ℂ) * star (W : Matrix ι ι ℂ) *
        ((W : Matrix ι ι ℂ) * D * star (W : Matrix ι ι ℂ)) *
          ((W : Matrix ι ι ℂ) * star (V : Matrix ι ι ℂ))
      = V * (star (W : Matrix ι ι ℂ) * W) * D * (star (W : Matrix ι ι ℂ) * W) *
          star (V : Matrix ι ι ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.mul_one, Matrix.mul_one]

variable (ι) in
/-- The real diagonal matrix `diag(s)` of a list `s` indexed by `Fin n`, transported to the index
type `ι` along the equivalence used by `Matrix.IsHermitian.eigenvalues`. For decreasing `s` its
eigenvalue list is `s` (`TauCeti.eigenvalues₀_unitaryChamberDiagonal`). -/
def unitaryChamberDiagonal (s : Fin (Fintype.card ι) → ℝ) :
    selfAdjoint.submodule ℝ (Matrix ι ι ℂ) :=
  ⟨diagonal fun k ↦ (s ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) : ℂ),
    (isHermitian_diagonal_iff.mpr fun _ ↦ conj_ofReal _).isSelfAdjoint⟩

@[simp]
theorem coe_unitaryChamberDiagonal (s : Fin (Fintype.card ι) → ℝ) :
    (unitaryChamberDiagonal ι s : Matrix ι ι ℂ) =
      diagonal fun k ↦ (s ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm k) : ℂ) :=
  (rfl)

/-- **A decreasing list is the eigenvalue list of its diagonal matrix.** -/
theorem eigenvalues₀_unitaryChamberDiagonal {s : Fin (Fintype.card ι) → ℝ} (hs : Antitone s) :
    hermitianEigenvalues₀ (unitaryChamberDiagonal ι s) = s := by
  set e := Fintype.equivOfCardEq (α := Fin (Fintype.card ι)) (β := ι) (Fintype.card_fin _)
  rw [← List.ofFn_inj, ← IsHermitian.sort_roots_charpoly_eq_eigenvalues₀,
    coe_unitaryChamberDiagonal, charpoly_diagonal, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, RCLike.re_to_complex, ofReal_re]
  rw [show (Finset.univ.val.map fun k ↦ s (e.symm k)) = Finset.univ.val.map s by
    rw [← Multiset.map_univ_val_equiv e.symm, Multiset.map_map, Function.comp_def]]
  rw [Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hs.sortedGE_ofFn

/-! ### The orbit space -/

variable (ι) in
/-- **The orbit space of the coadjoint action of `U(n)` is the closed Weyl chamber.** The decreasing
eigenvalue list is a homeomorphism from the orbit space of the conjugation action of `U(n)` on the
Hermitian matrices onto the decreasing lists, the closed positive chamber of `𝔱* = ℝⁿ`. Its inverse
sends `s` to the orbit of the diagonal matrix `diag(s)`. -/
def unitaryConjOrbitHomeomorph :
    Quotient (unitaryConjRepresentation ι).orbitRel ≃ₜ
      {s : Fin (Fintype.card ι) → ℝ // Antitone s} where
  toFun := Quotient.lift (fun H ↦ ⟨hermitianEigenvalues₀ H, IsHermitian.eigenvalues₀_antitone _⟩)
    fun _ _ h ↦ Subtype.ext (unitaryConjRepresentation_orbitRel_iff.mp h)
  invFun s := Quotient.mk _ (unitaryChamberDiagonal ι s)
  left_inv := by
    rintro ⟨H⟩
    exact Quotient.sound (unitaryConjRepresentation_orbitRel_iff.mpr
      (eigenvalues₀_unitaryChamberDiagonal (IsHermitian.eigenvalues₀_antitone
        (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).isHermitian)))
  right_inv s := Subtype.ext (eigenvalues₀_unitaryChamberDiagonal s.property)
  continuous_toFun := by
    refine continuous_quot_lift _ (Continuous.subtype_mk ?_ _)
    exact continuous_eigenvalues₀.comp
      (Continuous.subtype_mk continuous_subtypeVal fun H ↦
        (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).isHermitian)
  continuous_invFun := continuous_quot_mk.comp (Continuous.subtype_mk (Continuous.matrix_diagonal
    (continuous_pi fun _ ↦
      continuous_ofReal.comp ((continuous_apply _).comp continuous_subtypeVal))) _)

@[simp]
theorem unitaryConjOrbitHomeomorph_mk (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    (unitaryConjOrbitHomeomorph ι (Quotient.mk _ H) : Fin (Fintype.card ι) → ℝ) =
      hermitianEigenvalues₀ H :=
  (rfl)

@[simp]
theorem unitaryConjOrbitHomeomorph_symm_apply (s : {s : Fin (Fintype.card ι) → ℝ // Antitone s}) :
    (unitaryConjOrbitHomeomorph ι).symm s = Quotient.mk _ (unitaryChamberDiagonal ι s) :=
  (rfl)

/-! ### Coadjoint orbits -/

variable (ι) in
/-- **The trace pairing identifies the conjugation orbits with the coadjoint orbits**: the orbit of
`H` under conjugation corresponds to the coadjoint orbit of `⟨H, ·⟩`. -/
def unitaryConjOrbitEquivCoadjointOrbit :
    Quotient (unitaryConjRepresentation ι).orbitRel ≃
      Quotient (unitaryCoadjointRepresentation ι).orbitRel :=
  Quotient.congr (unitaryTracePairingEquiv ι).toEquiv fun H K ↦ by
    simp only [Representation.orbitRel_apply, LinearEquiv.coe_toEquiv,
      unitaryTracePairingEquiv_apply, ← unitaryTracePairing_unitaryConjRepresentation]
    exact exists_congr fun U ↦ (unitaryTracePairing_injective (ι := ι)).eq_iff.symm

@[simp]
theorem unitaryConjOrbitEquivCoadjointOrbit_mk (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    unitaryConjOrbitEquivCoadjointOrbit ι (Quotient.mk _ H) =
      Quotient.mk _ (unitaryTracePairing ι H) := by
  rw [unitaryConjOrbitEquivCoadjointOrbit, Quotient.congr_mk, LinearEquiv.coe_toEquiv,
    unitaryTracePairingEquiv_apply]

variable (ι) in
/-- **The coadjoint orbits of `U(n)` are parametrized by the closed Weyl chamber.** Read through
the trace pairing, the coadjoint orbit of `⟨H, ·⟩` corresponds to the decreasing eigenvalue list
of `H` (`TauCeti.unitaryCoadjointOrbitEquiv_mk`), and a decreasing list `s` to the orbit of the
torus-fixed covector `⟨diag(s), ·⟩` (`TauCeti.unitaryCoadjointOrbitEquiv_symm_apply`). -/
def unitaryCoadjointOrbitEquiv :
    Quotient (unitaryCoadjointRepresentation ι).orbitRel ≃
      {s : Fin (Fintype.card ι) → ℝ // Antitone s} :=
  (unitaryConjOrbitEquivCoadjointOrbit ι).symm.trans (unitaryConjOrbitHomeomorph ι).toEquiv

@[simp]
theorem unitaryCoadjointOrbitEquiv_mk (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    (unitaryCoadjointOrbitEquiv ι (Quotient.mk _ (unitaryTracePairing ι H)) :
        Fin (Fintype.card ι) → ℝ) =
      hermitianEigenvalues₀ H := by
  rw [unitaryCoadjointOrbitEquiv, Equiv.trans_apply, ← unitaryConjOrbitEquivCoadjointOrbit_mk,
    Equiv.symm_apply_apply, Homeomorph.coe_toEquiv, unitaryConjOrbitHomeomorph_mk]

@[simp]
theorem unitaryCoadjointOrbitEquiv_symm_apply (s : {s : Fin (Fintype.card ι) → ℝ // Antitone s}) :
    (unitaryCoadjointOrbitEquiv ι).symm s =
      Quotient.mk _ (unitaryTorusDualInclusion ι
        (s.val ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm)) := by
  rw [unitaryCoadjointOrbitEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Homeomorph.coe_symm_toEquiv, unitaryConjOrbitHomeomorph_symm_apply,
    unitaryConjOrbitEquivCoadjointOrbit_mk, unitaryTorusDualInclusion_apply]
  rfl

/-- **The closed chamber is a fundamental domain for the coadjoint action of `U(n)`.** Every
coadjoint orbit contains the torus-fixed covector `⟨diag(s), ·⟩` of exactly one decreasing list
`s`. -/
theorem existsUnique_antitone_orbitRel_unitaryTorusDualInclusion
    (ν : Dual ℝ (unitaryLieAlgebra ι)) :
    ∃! s : Fin (Fintype.card ι) → ℝ, Antitone s ∧ (unitaryCoadjointRepresentation ι).orbitRel ν
      (unitaryTorusDualInclusion ι (s ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm)) := by
  have key (s : {s : Fin (Fintype.card ι) → ℝ // Antitone s}) :
      (unitaryCoadjointRepresentation ι).orbitRel ν
          (unitaryTorusDualInclusion ι
            (s.val ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm)) ↔
        unitaryCoadjointOrbitEquiv ι (Quotient.mk _ ν) = s := by
    rw [← Quotient.eq, ← unitaryCoadjointOrbitEquiv_symm_apply, Equiv.eq_symm_apply]
  refine ⟨unitaryCoadjointOrbitEquiv ι (Quotient.mk _ ν),
    ⟨(unitaryCoadjointOrbitEquiv ι (Quotient.mk _ ν)).property, (key _).2 rfl⟩, ?_⟩
  rintro s ⟨hs, hν⟩
  exact congrArg Subtype.val ((key ⟨s, hs⟩).1 hν).symm

end TauCeti
