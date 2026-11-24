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
(`TauCeti.unitaryCoadjointRepresentation_unitaryTracePairing`). Its orbit space
`Quotient (unitaryConjRepresentation ι).orbitRel` carries the quotient topology, and it is
Hausdorff since `U(n)` is compact. The topology is stated in this Hermitian model because
`Module.Dual` carries no topology.

* The decreasing eigenvalue list `Matrix.IsHermitian.eigenvalues₀` is constant on orbits, since
  unitary conjugation preserves the characteristic polynomial, which determines it
  (`Matrix.IsHermitian.eigenvalues₀_mul_mul_star`).
* Two Hermitian matrices with the same eigenvalue list are unitarily conjugate, by the spectral
  theorem (`Matrix.IsHermitian.exists_unitary_conj_of_eigenvalues₀_eq`), so the eigenvalue list
  classifies the orbits (`TauCeti.unitaryConjRepresentation_orbitRel_iff`).
* A decreasing list `s` is the eigenvalue list of the real diagonal matrix `diag(s)`
  (`TauCeti.hermitianEigenvalues₀_unitaryChamberDiagonal`).

Hence the eigenvalue list is a homeomorphism from the orbit space onto the closed chamber
`{s : Fin n → ℝ // Antitone s}` (`TauCeti.unitaryConjOrbitHomeomorph`). It is continuous because
the decreasing eigenvalues depend continuously on the matrix (`Matrix.continuous_eigenvalues₀`),
and its inverse `s ↦ [diag(s)]` is continuous, so no properness argument is needed. Read through
the trace pairing, this is the bijection between coadjoint orbits and the chamber
(`TauCeti.unitaryCoadjointOrbitEquiv`), whose inverse sends `s` to the orbit of the torus-fixed
covector `⟨diag(s), ·⟩` (`TauCeti.unitaryCoadjointOrbitEquiv_symm_apply`). Equivalently, every
coadjoint orbit contains `⟨diag(s), ·⟩` for exactly one decreasing `s`
(`TauCeti.existsUnique_antitone_orbitRel_unitaryTorusDualInclusion`).

As an informal remark, not formalized here: the center of `𝔲(n)` is the line `iℝ·1` of imaginary
scalar matrices, dual to the line of constant lists in `𝔱*`. The chamber is invariant under adding a
constant list, so it is the product of this central line with the decreasing lists of sum zero, the
closed chamber of `𝔰𝔲(n)`.

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
(`TauCeti.unitaryCoadjointRepresentation_unitaryTracePairing`). -/
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
  obtain ⟨U, hU, hKH⟩ := IsHermitian.exists_unitary_conj_of_eigenvalues₀_eq _ _ h.symm
  exact (Representation.orbitRel_apply _).mpr ⟨⟨U, hU⟩, Subtype.ext hKH.symm⟩

variable (ι) in
/-- The real diagonal matrix `diag(s)` of a list `s` indexed by `Fin n`, transported to the index
type `ι` along the equivalence used by `Matrix.IsHermitian.eigenvalues`. For decreasing `s` its
eigenvalue list is `s` (`TauCeti.hermitianEigenvalues₀_unitaryChamberDiagonal`). -/
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
theorem hermitianEigenvalues₀_unitaryChamberDiagonal {s : Fin (Fintype.card ι) → ℝ}
    (hs : Antitone s) : hermitianEigenvalues₀ (unitaryChamberDiagonal ι s) = s :=
  IsHermitian.eigenvalues₀_diagonal hs _

/-! ### The orbit space -/

variable (ι) in
/-- **The orbit space of the conjugation action of `U(n)` on Hermitian matrices is homeomorphic to
the closed Weyl chamber.** The decreasing eigenvalue list is a homeomorphism from this orbit space
onto the decreasing lists, the closed positive chamber of `𝔱* = ℝⁿ`. Its inverse sends `s` to the
orbit of the diagonal matrix `diag(s)`. On the coadjoint side this gives the bijection
`TauCeti.unitaryCoadjointOrbitEquiv`, since `Module.Dual` carries no topology. -/
def unitaryConjOrbitHomeomorph :
    Quotient (unitaryConjRepresentation ι).orbitRel ≃ₜ
      {s : Fin (Fintype.card ι) → ℝ // Antitone s} where
  toFun := Quotient.lift (fun H ↦ ⟨hermitianEigenvalues₀ H, IsHermitian.eigenvalues₀_antitone _⟩)
    fun _ _ h ↦ Subtype.ext (unitaryConjRepresentation_orbitRel_iff.mp h)
  invFun s := Quotient.mk _ (unitaryChamberDiagonal ι s)
  left_inv := by
    rintro ⟨H⟩
    exact Quotient.sound (unitaryConjRepresentation_orbitRel_iff.mpr
      (hermitianEigenvalues₀_unitaryChamberDiagonal (IsHermitian.eigenvalues₀_antitone
        (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).isHermitian)))
  right_inv s := Subtype.ext (hermitianEigenvalues₀_unitaryChamberDiagonal s.property)
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
      unitaryTracePairingEquiv_apply, unitaryCoadjointRepresentation_unitaryTracePairing]
    exact exists_congr fun U ↦ (unitaryTracePairing_injective (ι := ι)).eq_iff.symm

@[simp]
theorem unitaryConjOrbitEquivCoadjointOrbit_mk (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    unitaryConjOrbitEquivCoadjointOrbit ι (Quotient.mk _ H) =
      Quotient.mk _ (unitaryTracePairing ι H) := by
  rw [unitaryConjOrbitEquivCoadjointOrbit, Quotient.congr_mk, LinearEquiv.coe_toEquiv,
    unitaryTracePairingEquiv_apply]

variable (ι) in
/-- **The coadjoint orbits of `U(n)` are in bijection with the closed Weyl chamber.** Read through
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
  -- `unitaryChamberDiagonal ι s` is the diagonal matrix of `s ∘ e.symm`.
  exact congrArg _ (congrArg _ (Subtype.ext (coe_unitaryChamberDiagonal _)))

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
