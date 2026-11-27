/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonzeroVectors.Pi
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PrescribedRowColumn

/-!
# Direct and mirror data modulo `N`, and the operator `Up`

Let `A` be a commutative ring with a reduction `red : A →+* R` onto a finite ring `R`, and `F` an
`A`-algebra. In the application, `P` is a set of places above a prime `N` that splits completely
in a CM field `E`, one in each conjugate pair, `F = ∏_{w ∈ P} E_w`, `A` is its ring of integers
and `R = (ℤ/N)^P`. A *lift* from a representation `π` of `GL_m(F)` on `V` to a representation
`π'` of `GL_{m'}(F)` on `V'` is a map `L : (Matrix m' m R → k) →ₗ[k] V →ₗ[k] V'`, linear in a
*datum* `Ψ`, a function of the reduction of an integral `m' × m` matrix. The index types carry
distinguished indices `l : m` and `l' : m'`, the last indices. The data used are

* `lastColDatum k l z` and `lastRowDatum k l' y`, the indicators of the matrices whose column `l`
  is `z`, respectively whose row `l'` is `y`;
* the *direct datum* `directDatum k l l'`, the indicator of the matrices whose column `l` is the
  standard basis vector at `l'`;
* for a function `ψ : R → k`, the *mirror datum* `mirrorDatum ψ l l' : T ↦ ψ (T l' l)` and
  `charDatum ψ l' y : T ↦ ψ (T l' ⬝ᵥ y)`. In the application `ψ` is the character
  `c ↦ ψ_𝔸(-c / N)` of `(ℤ/N)^P` obtained from the standard additive character `ψ_𝔸` of the finite
  adeles; nothing below uses more than that `ψ` is a function.

For an element `D` of `GL_m(F)`, in the application `diag(1, …, 1, N⁻¹)` at the places of `P`, and
an *`Up`-family* `g` (`TauCeti.ThetaLift.IsUpFamily`: integral matrices `g y` whose reductions
have column `l` and row `l` equal to `y`), the operator `Up` is
`upOperator π D l g ψ = π(D) ∑_y ψ(y_l) π(g y)`, the sum over the vectors `y` of `m → R` whose
entry at `l` is a unit.

A lift *obeys the lift law with factor `γ`* (`TauCeti.ThetaLift.LiftLaw`) if it is equivariant
for the integral points acting on data through their reductions, `π'(b) L(Ψ^{a,b})(π(a) φ) = L(Ψ) φ`
with `Ψ^{a,b}(T) = Ψ(b T a)`, and `π'(D') L(Ψ_row) φ = γ · L(direct)(π(D) φ)` for the indicator
`Ψ_row` of the matrices whose row `l'` is the standard basis vector at `l`. For `R = P → 𝔽`, a
vector `φ` is *ramified* (`TauCeti.ThetaLift.IsRamified`) if, at every place `w ∈ P`, it is
`ψ - π(x) ψ` for an integral unit scalar `x` that is `1` modulo `N` at the other places.

The proofs expand the data over residues and apply the lift law term by term. On a ramified
vector, a lift kills every datum invariant under the scalings at one place
(`TauCeti.ThetaLift.LiftLaw.apply_eq_zero_of_isRamified`). This removes the residues whose corner
entry is not a unit, or whose column vanishes at some place; the lift law identifies each
remaining term with a direct lift or a lift by `Ψ_row`, moved by an integral matrix.

## Main definitions

* `TauCeti.ThetaLift.lastColDatum`, `TauCeti.ThetaLift.lastRowDatum`,
  `TauCeti.ThetaLift.directDatum`, `TauCeti.ThetaLift.mirrorDatum`, `TauCeti.ThetaLift.charDatum`:
  the data.
* `TauCeti.ThetaLift.IsUpFamily` and `TauCeti.ThetaLift.upOperator`: the operator `Up`.
* `TauCeti.ThetaLift.LiftLaw`: the lift law with factor `γ`.
* `TauCeti.ThetaLift.IsRamified`: ramified vectors.
* `TauCeti.ThetaLift.gluedLift`: the glued double lift `π''(D'') ∑_y L'(char_y) ∘ L(lastCol_y)`.
* `TauCeti.ThetaLift.directChain`, `TauCeti.ThetaLift.gluedChain`: the composites of the first
  lifts of a chain with direct data, and of its first glued double lifts.

## Main results

* `TauCeti.ThetaLift.exists_isUpFamily`: `Up`-families exist when the reduction is surjective
  and reflects units.
* `TauCeti.ThetaLift.LiftLaw.mirrorDatum_eq_upOperator_directDatum`,
  `TauCeti.ThetaLift.LiftLaw.mirrorDatum_eq_smul_directDatum_upOperator` and
  `TauCeti.ThetaLift.LiftLaw.upOperator_directDatum`: on ramified vectors,
  `π'(D') L(mirror) φ = Up(L(direct) φ) = γ · L(direct)(Up φ)`.
* `TauCeti.ThetaLift.LiftLaw.isRamified_apply`, `TauCeti.ThetaLift.IsRamified.upOperator` and
  `TauCeti.ThetaLift.IsRamified.upOperator_pow`: lifts, `Up` and its powers keep vectors ramified.
* `TauCeti.ThetaLift.LiftLaw.gluedLift_apply_eq_smul`: on ramified vectors, a glued double lift is
  `#prim · γ' γ` times the two direct lifts after `Up`, where `#prim` counts the primitive vectors
  (`TauCeti.primitiveVectors`, the vectors nonzero at every place).
* `TauCeti.ThetaLift.gluedChain_eq_smul_directChain`: on ramified vectors, the first `p` glued
  double lifts of a chain are `∏_{i<p} (d_i · #prim_i · ∏_{j<2i+2} γ_j)` times the first `2p`
  direct lifts after `Up^p`.

## References

* The formal proof whose route this follows: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (Apache 2.0), file `src/New/UpperBound/Objects/LiftLawsModuloN.lean`.
-/

public section

open Matrix Matrix.GeneralLinearGroup Finset

namespace TauCeti.ThetaLift

/-! ### Data on matrices over a residue ring -/

section Data

variable (k : Type*) {R m m' : Type*}

/-- The datum `lastColDatum k l z` on `m' × m` matrices: the indicator of the matrices whose
column `l` is `z`. -/
def lastColDatum [Zero k] [One k] [DecidableEq R] [Fintype m'] (l : m) (z : m' → R)
    (T : Matrix m' m R) : k :=
  if T.col l = z then 1 else 0

/-- The datum `lastRowDatum k l' y` on `m' × m` matrices: the indicator of the matrices whose
row `l'` is `y`. -/
def lastRowDatum [Zero k] [One k] [DecidableEq R] [Fintype m] (l' : m') (y : m → R)
    (T : Matrix m' m R) : k :=
  if T.row l' = y then 1 else 0

/-- The direct datum: the indicator of the matrices whose column `l` is the standard basis
vector at `l'`. -/
def directDatum [Zero k] [One k] [Zero R] [One R] [DecidableEq R] [Fintype m'] [DecidableEq m']
    (l : m) (l' : m') : Matrix m' m R → k :=
  lastColDatum k l (Pi.single l' 1)

variable {k}

/-- The mirror datum of `ψ : R → k`: the value of `ψ` at the entry `(l', l)` of a matrix. -/
def mirrorDatum (ψ : R → k) (l : m) (l' : m') (T : Matrix m' m R) : k :=
  ψ (T l' l)

/-- The datum `charDatum ψ l' y`: the value of `ψ` at the pairing of the row `l'` of a matrix
with `y`. -/
def charDatum [Fintype m] [Mul R] [AddCommMonoid R] (ψ : R → k) (l' : m') (y : m → R)
    (T : Matrix m' m R) : k :=
  ψ (T.row l' ⬝ᵥ y)

variable (k)

@[simp]
theorem lastColDatum_apply [Zero k] [One k] [DecidableEq R] [Fintype m'] (l : m) (z : m' → R)
    (T : Matrix m' m R) : lastColDatum k l z T = if T.col l = z then 1 else 0 :=
  (rfl)

@[simp]
theorem lastRowDatum_apply [Zero k] [One k] [DecidableEq R] [Fintype m] (l' : m') (y : m → R)
    (T : Matrix m' m R) : lastRowDatum k l' y T = if T.row l' = y then 1 else 0 :=
  (rfl)

theorem directDatum_def [Zero k] [One k] [Zero R] [One R] [DecidableEq R] [Fintype m']
    [DecidableEq m'] (l : m) (l' : m') :
    directDatum k l l' = lastColDatum k (R := R) l (Pi.single l' 1) :=
  (rfl)

variable {k}

@[simp]
theorem mirrorDatum_apply (ψ : R → k) (l : m) (l' : m') (T : Matrix m' m R) :
    mirrorDatum ψ l l' T = ψ (T l' l) :=
  (rfl)

@[simp]
theorem charDatum_apply [Fintype m] [Mul R] [AddCommMonoid R] (ψ : R → k) (l' : m') (y : m → R)
    (T : Matrix m' m R) : charDatum ψ l' y T = ψ (T.row l' ⬝ᵥ y) :=
  (rfl)

/-- The mirror datum is `charDatum` at the standard basis vector. -/
@[simp]
theorem charDatum_single_one [Fintype m] [DecidableEq m] [NonAssocSemiring R] (ψ : R → k)
    (l : m) (l' : m') : charDatum ψ l' (Pi.single l 1) = mirrorDatum ψ l l' := by
  ext T
  simp

variable (k) in
/-- Multiplying on the left by an invertible matrix `M` moves the prescribed column `z` to
`M z`. -/
theorem lastColDatum_mul_left [Zero k] [One k] [Semiring R] [DecidableEq R] [Fintype m']
    [DecidableEq m'] (l : m) {M : Matrix m' m' R} (hM : IsUnit M) (z : m' → R)
    (T : Matrix m' m R) : lastColDatum k l (M *ᵥ z) (M * T) = lastColDatum k l z T := by
  simp [col_mul_eq_mulVec_col, (mulVec_injective_of_isUnit hM).eq_iff]

variable (k) in
/-- Multiplying on the right by an invertible matrix `M` moves the prescribed row `y` to
`y M`. -/
theorem lastRowDatum_mul_right [Zero k] [One k] [Semiring R] [DecidableEq R] [Fintype m]
    [DecidableEq m] (l' : m') {M : Matrix m m R} (hM : IsUnit M) (y : m → R)
    (T : Matrix m' m R) : lastRowDatum k l' (y ᵥ* M) (T * M) = lastRowDatum k l' y T := by
  simp [row_mul_eq_vecMul_row, (vecMul_injective_of_isUnit hM).eq_iff]

/-- The mirror datum of a product `T M` is `charDatum` at the column `l` of `M`. -/
theorem mirrorDatum_mul_right [Fintype m] [Mul R] [AddCommMonoid R] (ψ : R → k) (l : m) (l' : m')
    (M : Matrix m m R) (T : Matrix m' m R) :
    mirrorDatum ψ l l' (T * M) = charDatum ψ l' (M.col l) T := by
  rw [mirrorDatum_apply, charDatum_apply, mul_apply', row_apply', col_apply']

variable [Semiring k] [Monoid R] [Fintype R] [DecidableEq R]

/-- The sum over the vectors `z` with a unit entry at `l'` of `ψ(z_{l'})` times the indicator of
column `l` equal to `z` is `ψ` of the entry `(l', l)` where that entry is a unit, and `0`
elsewhere. -/
theorem sum_smul_lastColDatum [Fintype m'] [DecidableEq m'] (ψ : R → k) (l : m) (l' : m') :
    ∑ z ∈ univ.filter (fun z : m' → R ↦ IsUnit (z l')), ψ (z l') • lastColDatum k l z =
      fun T ↦ if IsUnit (T l' l) then ψ (T l' l) else 0 := by
  ext T
  simp only [Finset.sum_apply, Pi.smul_apply, lastColDatum_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- The row analogue of `TauCeti.ThetaLift.sum_smul_lastColDatum`. -/
theorem sum_smul_lastRowDatum [Fintype m] [DecidableEq m] (ψ : R → k) (l : m) (l' : m') :
    ∑ y ∈ univ.filter (fun y : m → R ↦ IsUnit (y l)), ψ (y l) • lastRowDatum k l' y =
      fun T : Matrix m' m R ↦ if IsUnit (T l' l) then ψ (T l' l) else 0 := by
  ext T
  simp only [Finset.sum_apply, Pi.smul_apply, lastRowDatum_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  simp

end Data

/-! ### The operator `Up` -/

section UpFamily

variable {k A F R : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [CommRing R]
  {m : Type*} [Fintype m] [DecidableEq m] {V : Type*} [AddCommGroup V] [Module k V]

/-- A family `g` of integral matrices is an *`Up`-family* at the index `l` if, for every vector
`y` of `m → R` with a unit entry at `l`, the reduction of `g y` has `y` as its column `l` and as
its row `l`. -/
structure IsUpFamily (red : A →+* R) (l : m) (g : (m → R) → GL m A) : Prop where
  col_eq (y : m → R) (hy : IsUnit (y l)) : (map red (g y) : Matrix m m R).col l = y
  row_eq (y : m → R) (hy : IsUnit (y l)) : (map red (g y) : Matrix m m R).row l = y

/-- `Up`-families exist when the reduction is surjective and reflects units, as the reduction
of a product of complete local rings onto their residue fields does. -/
theorem exists_isUpFamily (red : A →+* R) [IsLocalHom red] (hred : Function.Surjective red)
    (l : m) : ∃ g : (m → R) → GL m A, IsUpFamily red l g := by
  have (y : m → R) : ∃ a : GL m A, IsUnit (y l) →
      (map red a : Matrix m m R).col l = y ∧ (map red a : Matrix m m R).row l = y := by
    by_cases hy : IsUnit (y l)
    · obtain ⟨M, hM⟩ := exists_col_eq_and_row_eq_of_isUnit (u := y) (v := y) rfl hy
      obtain ⟨a, rfl⟩ := map_surjective red hred M
      exact ⟨a, fun _ ↦ hM⟩
    · exact ⟨1, fun h ↦ (hy h).elim⟩
  choose g hg using this
  exact ⟨g, ⟨fun y hy ↦ (hg y hy).1, fun y hy ↦ (hg y hy).2⟩⟩

end UpFamily

section UpOperator

variable {k A F R : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [Monoid R]
  [Fintype R] [DecidableEq R] {m : Type*} [Fintype m] [DecidableEq m] {V : Type*}
  [AddCommGroup V] [Module k V]

/-- The operator `Up = π(D) ∑_y ψ(y_l) π(g_y)` on a representation `π` of `GL_m(F)`, the sum over
the vectors `y` of `m → R` whose entry at `l` is a unit. Here `g` is an integral family, in the
application an `Up`-family (`TauCeti.ThetaLift.IsUpFamily`), and `D` an element of `GL_m(F)`,
in the application `diag(1, …, 1, N⁻¹)` at the places above `N`. -/
def upOperator (π : Representation k (GL m F) V) (D : GL m F) (l : m) (g : (m → R) → GL m A)
    (ψ : R → k) : V →ₗ[k] V :=
  π D ∘ₗ ∑ y ∈ univ.filter (fun y : m → R ↦ IsUnit (y l)),
    ψ (y l) • π (map (algebraMap A F) (g y))

theorem upOperator_apply (π : Representation k (GL m F) V) (D : GL m F) (l : m)
    (g : (m → R) → GL m A) (ψ : R → k) (φ : V) :
    upOperator π D l g ψ φ =
      π D (∑ y ∈ univ.filter (fun y : m → R ↦ IsUnit (y l)),
        ψ (y l) • π (map (algebraMap A F) (g y)) φ) := by
  simp [upOperator]

/-- `Up` commutes with the integral unit scalars, which are central. -/
theorem upOperator_map_scalar (π : Representation k (GL m F) V) (D : GL m F) (l : m)
    (g : (m → R) → GL m A) (ψ : R → k) (u : Aˣ) (φ : V) :
    upOperator π D l g ψ (π (map (algebraMap A F) (scalar m u)) φ) =
      π (map (algebraMap A F) (scalar m u)) (upOperator π D l g ψ φ) := by
  have hc (h : GL m F) (v : V) :
      π h (π (map (algebraMap A F) (scalar m u)) v) =
        π (map (algebraMap A F) (scalar m u)) (π h v) := by
    rw [← mul_apply_eq_comp, ← map_mul, map_scalar, ← GeneralLinearGroup.scalar_commute,
      map_mul, mul_apply_eq_comp]
  simp only [upOperator_apply, hc, ← map_smul, ← map_sum]

end UpOperator

/-! ### The lift law -/

section LiftLaw

variable {k A F R : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [CommRing R]
  [DecidableEq R] {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
  {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- A lift `L` from a representation `π` of `GL_m(F)` to a representation `π'` of `GL_{m'}(F)`,
linear in a datum `Ψ` on the `m' × m` matrices over the residue ring `R`, *obeys the lift law
with factor `γ`* if
* it is equivariant for the integral points acting through their reductions:
  `π'(b) L(Ψ^{a,b})(π(a) φ) = L(Ψ) φ` for integral invertible `a`, `b`, where
  `Ψ^{a,b}(T) = Ψ(b T a)`;
* `π'(D') L(Ψ_row) φ = γ L(direct)(π(D) φ)`, where `Ψ_row` is the indicator of the matrices whose
  row `l'` is the standard basis vector at `l`, and `direct` is the direct datum. -/
structure LiftLaw (red : A →+* R) (π : Representation k (GL m F) V)
    (π' : Representation k (GL m' F) V') (D : GL m F) (D' : GL m' F) (l : m) (l' : m')
    (L : (Matrix m' m R → k) →ₗ[k] V →ₗ[k] V') (γ : k) : Prop where
  equivariant (a : GL m A) (b : GL m' A) (Ψ : Matrix m' m R → k) (φ : V) :
    π' (map (algebraMap A F) b)
        (L (fun T ↦ Ψ ((map red b : Matrix m' m' R) * T * (map red a : Matrix m m R)))
          (π (map (algebraMap A F) a) φ)) = L Ψ φ
  pole (φ : V) :
    π' D' (L (lastRowDatum k l' (Pi.single l 1)) φ) = γ • L (directDatum k l l') (π D φ)

namespace LiftLaw

variable {red : A →+* R} {π : Representation k (GL m F) V} {π' : Representation k (GL m' F) V'}
  {D : GL m F} {D' : GL m' F} {l : m} {l' : m'} {L : (Matrix m' m R → k) →ₗ[k] V →ₗ[k] V'}
  {γ : k}

/-- The lift law for an integral point of the source alone. -/
theorem apply_mul_right (hL : LiftLaw red π π' D D' l l' L γ) (a : GL m A)
    (Ψ : Matrix m' m R → k) (φ : V) :
    L (fun T ↦ Ψ (T * (map red a : Matrix m m R))) (π (map (algebraMap A F) a) φ) = L Ψ φ := by
  simpa using hL.equivariant a 1 Ψ φ

/-- The lift law for an integral point of the target alone. -/
theorem map_apply_mul_left (hL : LiftLaw red π π' D D' l l' L γ) (b : GL m' A)
    (Ψ : Matrix m' m R → k) (φ : V) :
    π' (map (algebraMap A F) b) (L (fun T ↦ Ψ ((map red b : Matrix m' m' R) * T)) φ) =
      L Ψ φ := by
  simpa using hL.equivariant 1 b Ψ φ

/-- The lift by the indicator of a column `l` equal to the column `l'` of the reduction of `b`
is the direct lift moved by `b`. -/
theorem apply_lastColDatum_col (hL : LiftLaw red π π' D D' l l' L γ) (b : GL m' A) (φ : V) :
    L (lastColDatum k l ((map red b : Matrix m' m' R).col l')) φ =
      π' (map (algebraMap A F) b) (L (directDatum k l l') φ) := by
  rw [← hL.map_apply_mul_left b (lastColDatum k l _) φ, ← mulVec_single_one, directDatum_def]
  simp_rw [lastColDatum_mul_left k l (map red b).isUnit]

/-- The lift by the indicator of a row `l'` equal to the row `l` of the reduction of `a` is the
lift by `Ψ_row` after `a`. -/
theorem apply_lastRowDatum_row (hL : LiftLaw red π π' D D' l l' L γ) (a : GL m A) (φ : V) :
    L (lastRowDatum k l' ((map red a : Matrix m m R).row l)) φ =
      L (lastRowDatum k l' (Pi.single l 1)) (π (map (algebraMap A F) a) φ) := by
  rw [← hL.apply_mul_right a (lastRowDatum k l' _) φ, ← single_one_vecMul]
  simp_rw [lastRowDatum_mul_right k l' (map red a).isUnit]

/-- After an integral point `a`, the lift by `charDatum` at the column `l` of the reduction of
`a` is the lift by the mirror datum. -/
theorem apply_charDatum_col (hL : LiftLaw red π π' D D' l l' L γ) (ψ : R → k) (a : GL m A)
    (φ : V) :
    L (charDatum ψ l' ((map red a : Matrix m m R).col l)) (π (map (algebraMap A F) a) φ) =
      L (mirrorDatum ψ l l') φ := by
  rw [← hL.apply_mul_right a (mirrorDatum ψ l l') φ]
  simp_rw [mirrorDatum_mul_right]

/-- Lifts commute with the integral unit scalars. -/
theorem apply_map_scalar (hL : LiftLaw red π π' D D' l l' L γ) (u : Aˣ) (Ψ : Matrix m' m R → k)
    (φ : V) :
    L Ψ (π (map (algebraMap A F) (scalar m u)) φ) =
      π' (map (algebraMap A F) (scalar m' u)) (L Ψ φ) := by
  have h := hL.equivariant (scalar m u) (scalar m' u⁻¹) Ψ φ
  have hT (T : Matrix m' m R) :
      (map red (scalar m' u⁻¹) : Matrix m' m' R) * T * (map red (scalar m u) : Matrix m m R) =
        T := by
    simp only [map_scalar, coe_scalar, Matrix.scalar_apply, ← smul_eq_diagonal_mul,
      ← smul_eq_mul_diagonal, smul_smul]
    simp [← map_mul]
  simp only [hT] at h
  have h1 : map (algebraMap A F) (scalar m' u) * map (algebraMap A F) (scalar m' u⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  rw [← h, ← mul_apply_eq_comp, ← map_mul, h1, map_one, one_apply_eq_self]

end LiftLaw

end LiftLaw

/-! ### Ramified vectors -/

section Ramified

variable {k A F P 𝔽 : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [CommRing 𝔽]
  {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
  {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- A vector `φ` of a representation `π` of `GL_m(F)` is *ramified* for the reduction
`red : A →+* (P → 𝔽)` if, for every place `w ∈ P`, `φ = ψ - π(x) ψ` for a vector `ψ` and an
integral unit scalar `x` whose reduction is `1` at every place other than `w`. -/
def IsRamified (red : A →+* (P → 𝔽)) (π : Representation k (GL m F) V) (φ : V) : Prop :=
  ∀ w : P, ∃ (u : Aˣ) (ψ : V), (∀ w' ≠ w, red u w' = 1) ∧
    φ = ψ - π (map (algebraMap A F) (scalar m u)) ψ

/-- The defining property of a ramified vector. -/
theorem isRamified_iff {red : A →+* (P → 𝔽)} {π : Representation k (GL m F) V} {φ : V} :
    IsRamified red π φ ↔ ∀ w : P, ∃ (u : Aˣ) (ψ : V), (∀ w' ≠ w, red u w' = 1) ∧
      φ = ψ - π (map (algebraMap A F) (scalar m u)) ψ :=
  Iff.rfl

/-- `Up` keeps ramified vectors ramified. -/
theorem IsRamified.upOperator [Fintype P] [DecidableEq P] [Fintype 𝔽] [DecidableEq 𝔽]
    {red : A →+* (P → 𝔽)} {π : Representation k (GL m F) V}
    {φ : V} (hφ : IsRamified red π φ) (D : GL m F) (l : m) (g : (m → P → 𝔽) → GL m A)
    (ψ : (P → 𝔽) → k) : IsRamified red π (ThetaLift.upOperator π D l g ψ φ) := by
  intro w
  obtain ⟨u, ψ', hu, rfl⟩ := hφ w
  exact ⟨u, ThetaLift.upOperator π D l g ψ ψ', hu, by rw [map_sub, upOperator_map_scalar]⟩

/-- The powers of `Up` keep ramified vectors ramified. -/
theorem IsRamified.upOperator_pow [Fintype P] [DecidableEq P] [Fintype 𝔽] [DecidableEq 𝔽]
    {red : A →+* (P → 𝔽)} {π : Representation k (GL m F) V}
    {φ : V} (hφ : IsRamified red π φ) (D : GL m F) (l : m) (g : (m → P → 𝔽) → GL m A)
    (ψ : (P → 𝔽) → k) (q : ℕ) : IsRamified red π ((ThetaLift.upOperator π D l g ψ ^ q) φ) := by
  induction q with
  | zero => simpa using hφ
  | succ q ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact ih.upOperator _ _ _ _

/-- Lifts keep ramified vectors ramified. -/
theorem LiftLaw.isRamified_apply [Fintype P] [DecidableEq 𝔽] {red : A →+* (P → 𝔽)}
    {π : Representation k (GL m F) V} {π' : Representation k (GL m' F) V'} {D : GL m F}
    {D' : GL m' F} {l : m} {l' : m'} {L : (Matrix m' m (P → 𝔽) → k) →ₗ[k] V →ₗ[k] V'} {γ : k}
    {φ : V} (hL : LiftLaw red π π' D D' l l' L γ) (hφ : IsRamified red π φ)
    (Ψ : Matrix m' m (P → 𝔽) → k) : IsRamified red π' (L Ψ φ) := by
  intro w
  obtain ⟨u, ψ, hu, rfl⟩ := hφ w
  exact ⟨u, L Ψ ψ, hu, by rw [map_sub, hL.apply_map_scalar]⟩

end Ramified

/-! ### The lift laws at the places `P` -/

section Places

variable {k A F P 𝔽 : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [Field 𝔽]
  {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
  {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [Fintype P] [DecidableEq P] [Fintype 𝔽] [DecidableEq 𝔽]

omit [Fintype m] [DecidableEq m] [DecidableEq m'] [Fintype 𝔽] in
variable (k) in
/-- The indicator of a column `z` that vanishes at the place `w` is invariant under the scalings
at `w`. -/
theorem lastColDatum_mulSingle_smul (l : m) {z : m' → P → 𝔽} {w : P} (hz : ∀ i, z i w = 0)
    {t : 𝔽} (ht : t ≠ 0) (T : Matrix m' m (P → 𝔽)) :
    lastColDatum k l z ((Pi.mulSingle w t : P → 𝔽) • T) = lastColDatum k l z T := by
  simp only [lastColDatum_apply]
  congr 1
  simp only [eq_iff_iff, funext_iff, col_apply]
  refine forall_congr' fun i ↦ forall_congr' fun w' ↦ ?_
  by_cases h : w' = w
  · subst h
    simp [hz, ht]
  · simp [h]

namespace LiftLaw

variable {red : A →+* (P → 𝔽)} {π : Representation k (GL m F) V}
  {π' : Representation k (GL m' F) V'} {D : GL m F} {D' : GL m' F} {l : m} {l' : m'}
  {L : (Matrix m' m (P → 𝔽) → k) →ₗ[k] V →ₗ[k] V'} {γ : k} {φ : V}

omit [Fintype 𝔽] in
/-- On a ramified vector, a lift kills every datum that is invariant under the scalings at one
place. -/
theorem apply_eq_zero_of_isRamified (hL : LiftLaw red π π' D D' l l' L γ)
    (hφ : IsRamified red π φ) (w : P) {Ψ : Matrix m' m (P → 𝔽) → k}
    (hΨ : ∀ t : 𝔽, t ≠ 0 → ∀ T, Ψ ((Pi.mulSingle w t : P → 𝔽) • T) = Ψ T) : L Ψ φ = 0 := by
  obtain ⟨u, ψ, hu, rfl⟩ := hφ w
  have hred : red u = Pi.mulSingle w (red u w) := by
    ext w'
    by_cases h : w' = w
    · subst h
      simp
    · simp [h, hu w' h]
  have hne : red u w ≠ 0 := (Pi.isUnit_iff.1 (u.isUnit.map red) w).ne_zero
  have hT (T : Matrix m' m (P → 𝔽)) :
      T * (map red (scalar m u) : Matrix m m (P → 𝔽)) =
        (Pi.mulSingle w (red u w) : P → 𝔽) • T := by
    rw [map_scalar, coe_scalar, Units.coe_map, MonoidHom.coe_ofClass, ← hred,
      Matrix.scalar_apply, smul_eq_mul_diagonal]
  rw [map_sub, sub_eq_zero, ← hL.apply_mul_right (scalar m u) Ψ ψ]
  simp only [hT, hΨ _ hne]

/-- On a ramified vector, a lift kills every function of the entry `(l', l)` that vanishes where
that entry is a unit. -/
theorem apply_ite_isUnit_zero_eq_zero (hL : LiftLaw red π π' D D' l l' L γ)
    (hφ : IsRamified red π φ) (f : (P → 𝔽) → k) :
    L (fun T ↦ if IsUnit (T l' l) then 0 else f (T l' l)) φ = 0 := by
  classical
  have hunit (c : P → 𝔽) : IsUnit c ↔ ¬ ∃ w, c w = 0 := by
    simp [Pi.isUnit_iff, isUnit_iff_ne_zero]
  -- split the datum along a place where the entry `(l', l)` vanishes
  let θ (w : P) (c : P → 𝔽) : k :=
    if h : ∃ w, c w = 0 then (if h.choose = w then f c else 0) else 0
  have hθ (w : P) (c : P → 𝔽) (hc : c w ≠ 0) : θ w c = 0 := by
    simp only [θ]
    split_ifs with h h'
    · exact (hc (h' ▸ h.choose_spec)).elim
    · rfl
    · rfl
  have hsum : (fun T : Matrix m' m (P → 𝔽) ↦ if IsUnit (T l' l) then 0 else f (T l' l)) =
      ∑ w, fun T ↦ θ w (T l' l) := by
    ext T
    rw [Finset.sum_apply]
    by_cases h : ∃ w, T l' l w = 0
    · have hT : ¬IsUnit (T l' l) := by rw [hunit]; exact not_not.2 h
      simp [θ, h, hT]
    · have hT : IsUnit (T l' l) := (hunit _).2 h
      simp [θ, h, hT]
  rw [hsum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun w _ ↦ hL.apply_eq_zero_of_isRamified hφ w fun t ht T ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases hc : T l' l w = 0
  · congr 1
    ext w'
    by_cases h : w' = w
    · subst h
      simp [hc]
    · simp [h]
  · rw [hθ w _ hc, hθ w _ (by simpa [ht] using hc)]

/-- On a ramified vector, the mirror datum may be restricted to the matrices whose entry
`(l', l)` is a unit. -/
theorem apply_mirrorDatum (hL : LiftLaw red π π' D D' l l' L γ) (hφ : IsRamified red π φ)
    (ψ : (P → 𝔽) → k) :
    L (mirrorDatum ψ l l') φ = L (fun T ↦ if IsUnit (T l' l) then ψ (T l' l) else 0) φ := by
  have h : mirrorDatum ψ l l' = (fun T ↦ if IsUnit (T l' l) then ψ (T l' l) else 0) +
      fun T ↦ if IsUnit (T l' l) then 0 else ψ (T l' l) := by
    ext T
    simp only [mirrorDatum_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h, map_add, LinearMap.add_apply, hL.apply_ite_isUnit_zero_eq_zero hφ, add_zero]

/-- **The mirror lift as `Up` after the direct lift.** On a ramified vector,
`π'(D') L(mirror) φ = Up(L(direct) φ)`, for any `Up`-family `g'` of the target. -/
theorem mirrorDatum_eq_upOperator_directDatum (hL : LiftLaw red π π' D D' l l' L γ)
    {g' : (m' → P → 𝔽) → GL m' A} (hg' : IsUpFamily red l' g') (hφ : IsRamified red π φ)
    (ψ : (P → 𝔽) → k) :
    π' D' (L (mirrorDatum ψ l l') φ) = upOperator π' D' l' g' ψ (L (directDatum k l l') φ) := by
  rw [hL.apply_mirrorDatum hφ, ← sum_smul_lastColDatum (R := P → 𝔽) ψ l l', upOperator_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have h := hL.apply_lastColDatum_col (g' z) φ
  rw [hg'.col_eq z (mem_filter.1 hz).2] at h
  rw [h]

/-- **`Up` after the mirror lift.** On a ramified vector,
`π'(D') L(mirror) φ = γ · L(direct)(Up φ)`, for any `Up`-family `g` of the source. -/
theorem mirrorDatum_eq_smul_directDatum_upOperator (hL : LiftLaw red π π' D D' l l' L γ)
    {g : (m → P → 𝔽) → GL m A} (hg : IsUpFamily red l g) (hφ : IsRamified red π φ)
    (ψ : (P → 𝔽) → k) :
    π' D' (L (mirrorDatum ψ l l') φ) = γ • L (directDatum k l l') (upOperator π D l g ψ φ) := by
  rw [upOperator_apply, ← hL.pole, hL.apply_mirrorDatum hφ,
    ← sum_smul_lastRowDatum (R := P → 𝔽) ψ l l']
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have h := hL.apply_lastRowDatum_row (g y) φ
  rw [hg.row_eq y (mem_filter.1 hy).2] at h
  rw [h]

/-- **`Up` passes through a direct lift at the cost `γ`.** On a ramified vector,
`Up(L(direct) φ) = γ · L(direct)(Up φ)`. -/
theorem upOperator_directDatum (hL : LiftLaw red π π' D D' l l' L γ)
    {g : (m → P → 𝔽) → GL m A} {g' : (m' → P → 𝔽) → GL m' A} (hg : IsUpFamily red l g)
    (hg' : IsUpFamily red l' g') (hφ : IsRamified red π φ) (ψ : (P → 𝔽) → k) :
    upOperator π' D' l' g' ψ (L (directDatum k l l') φ) =
      γ • L (directDatum k l l') (upOperator π D l g ψ φ) := by
  rw [← hL.mirrorDatum_eq_upOperator_directDatum hg' hφ,
    hL.mirrorDatum_eq_smul_directDatum_upOperator hg hφ]

end LiftLaw

end Places

/-! ### Glued double lifts -/

section Glued

variable {k F R : Type*} [CommRing k] [CommRing F] [Mul R] [AddCommMonoid R] [Fintype R]
  [DecidableEq R] {m m' m'' : Type*} [Fintype m'] [DecidableEq m'] [Fintype m''] [DecidableEq m'']
  {V V' V'' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V''] [Module k V'']

/-- The glued double lift `π''(D'') ∑_y L'(charDatum ψ l'' y) ∘ L(lastColDatum l y)` of two lifts
`L : V → V'` and `L' : V' → V''`, the sum over all vectors `y` of `m' → R`. -/
def gluedLift (π'' : Representation k (GL m'' F) V'') (D'' : GL m'' F)
    (L : (Matrix m' m R → k) →ₗ[k] V →ₗ[k] V') (L' : (Matrix m'' m' R → k) →ₗ[k] V' →ₗ[k] V'')
    (ψ : R → k) (l : m) (l'' : m'') : V →ₗ[k] V'' :=
  π'' D'' ∘ₗ ∑ y : m' → R, L' (charDatum ψ l'' y) ∘ₗ L (lastColDatum k l y)

theorem gluedLift_apply (π'' : Representation k (GL m'' F) V'') (D'' : GL m'' F)
    (L : (Matrix m' m R → k) →ₗ[k] V →ₗ[k] V') (L' : (Matrix m'' m' R → k) →ₗ[k] V' →ₗ[k] V'')
    (ψ : R → k) (l : m) (l'' : m'') (φ : V) :
    gluedLift π'' D'' L L' ψ l l'' φ =
      π'' D'' (∑ y : m' → R, L' (charDatum ψ l'' y) (L (lastColDatum k l y) φ)) := by
  simp [gluedLift]

end Glued

section GluedPlaces

variable {k A F P 𝔽 : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [Field 𝔽]
  [Fintype P] [DecidableEq P] [Fintype 𝔽] [DecidableEq 𝔽]
  {m m' m'' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] [Fintype m'']
  [DecidableEq m'']
  {V V' V'' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V''] [Module k V'']
  {red : A →+* (P → 𝔽)} {π : Representation k (GL m F) V} {π' : Representation k (GL m' F) V'}
  {π'' : Representation k (GL m'' F) V''} {D : GL m F} {D' : GL m' F} {D'' : GL m'' F} {l : m}
  {l' : m'} {l'' : m''} {L : (Matrix m' m (P → 𝔽) → k) →ₗ[k] V →ₗ[k] V'}
  {L' : (Matrix m'' m' (P → 𝔽) → k) →ₗ[k] V' →ₗ[k] V''} {γ γ' : k} {φ : V}

/-- **A glued double lift is a scalar times two direct lifts after `Up`.** For lifts obeying
the lift laws with factors `γ` and `γ'`, a ramified vector `φ` and an `Up`-family `g` of the
source,
`π''(D'') ∑_y L'(char_y) L(lastCol_y) φ = (#prim · γ' γ) · L'(direct) L(direct)(Up φ)`, where
`#prim` is the number of primitive vectors of `m' → P → 𝔽`. -/
theorem LiftLaw.gluedLift_apply_eq_smul [IsLocalHom red] (hred : Function.Surjective red)
    (hL : LiftLaw red π π' D D' l l' L γ) (hL' : LiftLaw red π' π'' D' D'' l' l'' L' γ')
    {g : (m → P → 𝔽) → GL m A} (hg : IsUpFamily red l g) (hφ : IsRamified red π φ)
    (ψ : (P → 𝔽) → k) :
    gluedLift π'' D'' L L' ψ l l'' φ =
      ((#(primitiveVectors m' P 𝔽) : k) * γ' * γ) •
        L' (directDatum k l' l'') (L (directDatum k l l') (upOperator π D l g ψ φ)) := by
  obtain ⟨g', hg'⟩ := exists_isUpFamily red hred l'
  have hterm (y : m' → P → 𝔽) :
      L' (charDatum ψ l'' y) (L (lastColDatum k l y) φ) =
        if y ∈ primitiveVectors m' P 𝔽 then
          L' (mirrorDatum ψ l' l'') (L (directDatum k l l') φ) else 0 := by
    split_ifs with hy
    · -- a primitive column is the column of an integral invertible matrix `b`
      obtain ⟨b, hb⟩ := exists_map_col_eq_of_mem_primitiveVectors red hred hy l'
      rw [← hb, hL.apply_lastColDatum_col, hL'.apply_charDatum_col]
    · -- a column vanishing at a place `w` gives a datum invariant under the scalings at `w`
      obtain ⟨w, hw⟩ : ∃ w, ∀ i, y i w = 0 := by simpa using hy
      rw [hL.apply_eq_zero_of_isRamified hφ w fun t ht T ↦
        lastColDatum_mulSingle_smul k l hw ht T, map_zero]
  rw [gluedLift_apply, Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_ite_mem, univ_inter,
    sum_const, ← Nat.cast_smul_eq_nsmul k]
  simp only [map_smul,
    hL'.mirrorDatum_eq_smul_directDatum_upOperator hg' (hL.isRamified_apply hφ _),
    hL.upOperator_directDatum hg hg' hφ, smul_smul, mul_assoc]

end GluedPlaces

/-! ### Chains of lifts -/

section Chain

variable {k F R : Type*} [CommRing k] [CommRing F] [DecidableEq R]
  {m : ℕ → Type*} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
  {V : ℕ → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]

section Direct

variable [Zero R] [One R]

/-- The composite `L_{n-1}(direct) ∘ ⋯ ∘ L_0(direct)` of the first `n` lifts of a chain, each
with its direct datum. -/
def directChain (L : ∀ j, (Matrix (m (j + 1)) (m j) R → k) →ₗ[k] V j →ₗ[k] V (j + 1))
    (l : ∀ j, m j) : ∀ n, V 0 →ₗ[k] V n
  | 0 => LinearMap.id
  | n + 1 => L n (directDatum k (l n) (l (n + 1))) ∘ₗ directChain L l n

@[simp]
theorem directChain_zero (L : ∀ j, (Matrix (m (j + 1)) (m j) R → k) →ₗ[k] V j →ₗ[k] V (j + 1))
    (l : ∀ j, m j) : directChain L l 0 = LinearMap.id :=
  (rfl)

@[simp]
theorem directChain_succ (L : ∀ j, (Matrix (m (j + 1)) (m j) R → k) →ₗ[k] V j →ₗ[k] V (j + 1))
    (l : ∀ j, m j) (n : ℕ) :
    directChain L l (n + 1) = L n (directDatum k (l n) (l (n + 1))) ∘ₗ directChain L l n :=
  (rfl)

end Direct

variable [Mul R] [AddCommMonoid R] [Fintype R]

/-- The composite of the first `p` glued double lifts of a chain, the double lift `i` being
`d_i · π(D) ∑_y L_{2i+1}(charDatum ψ y) ∘ L_{2i}(lastColDatum y)` from `V_{2i}` to
`V_{2i+2}` (`TauCeti.ThetaLift.gluedLift`). -/
def gluedChain (π : ∀ j, Representation k (GL (m j) F) (V j)) (D : ∀ j, GL (m j) F)
    (L : ∀ j, (Matrix (m (j + 1)) (m j) R → k) →ₗ[k] V j →ₗ[k] V (j + 1)) (l : ∀ j, m j)
    (ψ : R → k) (d : ℕ → k) : ∀ p, V 0 →ₗ[k] V (2 * p)
  | 0 => LinearMap.id
  | p + 1 => d p • gluedLift (π (2 * p + 1 + 1)) (D (2 * p + 1 + 1)) (L (2 * p)) (L (2 * p + 1))
      ψ (l (2 * p)) (l (2 * p + 1 + 1)) ∘ₗ gluedChain π D L l ψ d p

@[simp]
theorem gluedChain_zero (π : ∀ j, Representation k (GL (m j) F) (V j)) (D : ∀ j, GL (m j) F)
    (L : ∀ j, (Matrix (m (j + 1)) (m j) R → k) →ₗ[k] V j →ₗ[k] V (j + 1)) (l : ∀ j, m j)
    (ψ : R → k) (d : ℕ → k) : gluedChain π D L l ψ d 0 = LinearMap.id :=
  (rfl)

@[simp]
theorem gluedChain_succ (π : ∀ j, Representation k (GL (m j) F) (V j)) (D : ∀ j, GL (m j) F)
    (L : ∀ j, (Matrix (m (j + 1)) (m j) R → k) →ₗ[k] V j →ₗ[k] V (j + 1)) (l : ∀ j, m j)
    (ψ : R → k) (d : ℕ → k) (p : ℕ) :
    gluedChain π D L l ψ d (p + 1) =
      d p • gluedLift (π (2 * p + 1 + 1)) (D (2 * p + 1 + 1)) (L (2 * p)) (L (2 * p + 1)) ψ
        (l (2 * p)) (l (2 * p + 1 + 1)) ∘ₗ gluedChain π D L l ψ d p :=
  (rfl)

end Chain

section ChainPlaces

variable {k A F P 𝔽 : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F] [Field 𝔽]
  [Fintype P] [DecidableEq P] [Fintype 𝔽] [DecidableEq 𝔽]
  {m : ℕ → Type*} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
  {V : ℕ → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]
  {red : A →+* (P → 𝔽)} {π : ∀ j, Representation k (GL (m j) F) (V j)} {D : ∀ j, GL (m j) F}
  {l : ∀ j, m j} {L : ∀ j, (Matrix (m (j + 1)) (m j) (P → 𝔽) → k) →ₗ[k] V j →ₗ[k] V (j + 1)}
  {γ : ℕ → k} {φ : V 0}

omit [DecidableEq P] [Fintype 𝔽] in
/-- Chains of lifts obeying the lift laws keep ramified vectors ramified. -/
theorem isRamified_directChain
    (hL : ∀ j, LiftLaw red (π j) (π (j + 1)) (D j) (D (j + 1)) (l j) (l (j + 1)) (L j) (γ j))
    (hφ : IsRamified red (π 0) φ) (n : ℕ) : IsRamified red (π n) (directChain L l n φ) := by
  induction n with
  | zero => simpa using hφ
  | succ n ih => simpa using (hL n).isRamified_apply ih _

/-- **`Up` passes through a chain of direct lifts.** On a ramified vector, `Up` after the first
`n` direct lifts is `γ_0 ⋯ γ_{n-1}` times the chain after `Up`, for `Up`-families `G j` at
every level. -/
theorem upOperator_directChain
    (hL : ∀ j, LiftLaw red (π j) (π (j + 1)) (D j) (D (j + 1)) (l j) (l (j + 1)) (L j) (γ j))
    {G : ∀ j, (m j → P → 𝔽) → GL (m j) A} (hG : ∀ j, IsUpFamily red (l j) (G j))
    (hφ : IsRamified red (π 0) φ) (ψ : (P → 𝔽) → k) (n : ℕ) :
    upOperator (π n) (D n) (l n) (G n) ψ (directChain L l n φ) =
      (∏ j ∈ range n, γ j) • directChain L l n (upOperator (π 0) (D 0) (l 0) (G 0) ψ φ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [directChain_succ, LinearMap.comp_apply, LinearMap.comp_apply,
      (hL n).upOperator_directDatum (hG n) (hG (n + 1)) (isRamified_directChain hL hφ n), ih,
      map_smul, smul_smul, prod_range_succ, mul_comm]

/-- **Glued double lifts as direct lifts after a power of `Up`.** For a chain of lifts obeying the
lift laws with factors `γ_j`, a ramified vector `φ` and an `Up`-family `g` at level `0`, the
composite of the first `p` glued double lifts
`d_i · π(D) ∑_y L_{2i+1}(char_y) ∘ L_{2i}(lastCol_y)` takes `φ` to
`∏_{i<p} (d_i · #prim_i · ∏_{j<2i+2} γ_j)` times the first `2p` direct lifts of `Up^p φ`, where
`#prim_i` is the number of primitive vectors of `m_{2i+1} → P → 𝔽`. -/
theorem gluedChain_eq_smul_directChain [IsLocalHom red] (hred : Function.Surjective red)
    (hL : ∀ j, LiftLaw red (π j) (π (j + 1)) (D j) (D (j + 1)) (l j) (l (j + 1)) (L j) (γ j))
    {g : (m 0 → P → 𝔽) → GL (m 0) A} (hg : IsUpFamily red (l 0) g)
    (hφ : IsRamified red (π 0) φ) (ψ : (P → 𝔽) → k) (d : ℕ → k) (p : ℕ) :
    gluedChain π D L l ψ d p φ =
      (∏ i ∈ range p, (d i * #(primitiveVectors (m (2 * i + 1)) P 𝔽) *
        ∏ j ∈ range (2 * i + 2), γ j)) •
        directChain L l (2 * p) ((upOperator (π 0) (D 0) (l 0) g ψ ^ p) φ) := by
  classical
  -- `Up`-families at every level, equal to `g` at level `0`
  choose G hG using fun j ↦ exists_isUpFamily red hred (l j)
  set G' : ∀ j, (m j → P → 𝔽) → GL (m j) A := Function.update G 0 g
  have hG' (j : ℕ) : IsUpFamily red (l j) (G' j) := by
    rcases j with _ | j
    · simpa [G'] using hg
    · simpa [G'] using hG (j + 1)
  have hG'0 : G' 0 = g := by simp [G']
  induction p with
  | zero => simp
  | succ p ih =>
    have hp := hφ.upOperator_pow (D 0) (l 0) g ψ p
    have h := (hL (2 * p)).gluedLift_apply_eq_smul hred (hL (2 * p + 1)) (hG' (2 * p))
      (isRamified_directChain hL hp (2 * p)) ψ
    rw [upOperator_directChain hL hG' hp, hG'0] at h
    rw [gluedChain_succ, LinearMap.smul_apply, LinearMap.comp_apply, ih, map_smul, h, pow_succ',
      mul_apply_eq_comp]
    simp only [map_smul, smul_smul, prod_range_succ]
    congr 1
    ring

end ChainPlaces

end TauCeti.ThetaLift
