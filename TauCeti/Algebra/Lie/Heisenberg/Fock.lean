/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Algebra.Lie.Heisenberg.Loop
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.PDeriv
import TauCeti.RingTheory.Derivation.FirstOrder

/-!
# The Fock module of the Heisenberg Lie algebra

Let `H` be an abelian Lie algebra over an additively torsion-free commutative ring `R` and `B` a
symmetric bilinear form on `H`, possibly degenerate. The (uncharged) **Fock module** of the
Heisenberg Lie algebra `Heis = H[t, t⁻¹] ⊕ R K` of `TauCeti.loopHeisenberg` is the polynomial
algebra

`π = Sym(⊕_{j ≥ 0} H t^{-(j + 1)})`,

which we realise as `SymmetricAlgebra R (ℕ →₀ H)`, the generator `ι (single j h)` standing for the
negative mode `h(-(j + 1))` applied to the vacuum `1`. The modes act as follows
(`TauCeti.fockMode`):

* a **negative mode** `h(-(j + 1))` multiplies by the generator `ι (single j h)`;
* the **zero modes** act by zero;
* a **positive mode** `h(j + 1)` acts by `(j + 1)` times the derivation contracting each generator
  `k(-(j + 1))` against `h` by the form, `k(-(i + 1)) ↦ δ_{ij} B(h, k)`.

The central element `K` acts by the identity. The commutators of these operators are
`⁅h(m), k(n)⁆ = m B(h, k) δ_{m + n, 0}` (`TauCeti.lie_fockMode_fockMode`), which are the
Heisenberg relations with `K = 1`, so the assignment extends to a Lie algebra map `Heis → End π`
(`TauCeti.fockRepresentation`), making `π` a Lie module over `Heis`. Symmetry of `B` is used exactly
once, for the commutator of a negative mode with a positive one.

The vacuum `1` is killed by every mode `h(n)` with `n ≥ 0`, and
`h(n) k(-m) 1 = n B(h, k) δ_{n, m} 1` for `m, n > 0`. The vacuum generates `π` as a Lie module
(`TauCeti.lieSpan_one_fock`): iterated negative modes give all monomials of the polynomial algebra.

The **translation operator** `T` (`TauCeti.fockTranslation`) is the derivation of `π` with
`T(h(-(j + 1))) = (j + 1) h(-(j + 2))`. It kills the vacuum and satisfies the translation covariance
`⁅T, h(n)⁆ = -n h(n - 1)` (`TauCeti.lie_fockTranslation_fockMode`), the commutation relation that
the field `Y(h(-1)1, z) = Σ h(n) z^{-n-1}` of the free boson vertex algebra needs.

## Main definitions

* `TauCeti.fockCreation`, `TauCeti.fockContraction`, `TauCeti.fockAnnihilation`: the creation
  operators, the contraction derivations and the annihilation operators of the Fock space.
* `TauCeti.fockMode`: the operator by which the mode `h(n)` acts on the Fock space.
* `TauCeti.fockRepresentation`: the Lie algebra map `Heis → End π`; it underlies the instances
  `LieRingModule (loopHeisenberg B hB) (SymmetricAlgebra R (ℕ →₀ H))` and the `LieModule`
  instance.
* `TauCeti.fockTranslation`: the translation derivation `T` of the Fock space.

## Main results

* `TauCeti.lie_fockMode_fockMode`: the commutators of the mode operators.
* `TauCeti.heisenbergMode_lie_fock`, `TauCeti.centralElement_lie_fock`: modes act by `fockMode`
  and `K` acts by the identity.
* `TauCeti.heisenbergMode_lie_one_of_nonneg`: nonnegative modes kill the vacuum.
* `TauCeti.heisenbergMode_lie_heisenbergMode_lie_one`: `h(n) k(-m) 1 = n B(h, k) δ_{n, m} 1` for
  `m, n > 0`.
* `TauCeti.lieSpan_one_fock`: the vacuum generates the Fock module.
* `TauCeti.lie_fockTranslation_fockMode`: translation covariance `⁅T, h(n)⁆ = -n h(n - 1)`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §6.2.1, for the Fock representation
  of the Heisenberg Lie algebra.
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.5, for the free boson.
-/

public section

noncomputable section

open scoped TensorProduct
open LieAlgebra LieAlgebra.LoopAlgebra LieModule.Cohomology SymmetricAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

section Operators

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H] (B : LinearMap.BilinForm R H)

local notation "F" => SymmetricAlgebra R (ℕ →₀ H)

/-- The creation operator of the Fock space: multiplication by the generator
`ι (single j h)`, which represents the negative mode `h(-(j + 1))`. -/
def fockCreation (j : ℕ) : H →ₗ[R] Module.End R F :=
  LinearMap.mul R F ∘ₗ ι R (ℕ →₀ H) ∘ₗ Finsupp.lsingle j

/-- The creation operator multiplies by its generator. -/
@[simp]
theorem fockCreation_apply (j : ℕ) (h : H) (v : F) :
    fockCreation j h v = ι R (ℕ →₀ H) (Finsupp.single j h) * v :=
  (rfl)

/-- The contraction derivations of the Fock space at the index `j`: for `h : H` the derivation
sending the generator `ι (single i k)` to the scalar `B(h, k)` if `i = j`, and to zero
otherwise. -/
def fockContraction (j : ℕ) : H →ₗ[R] Derivation R F F :=
  pderiv ∘ₗ LinearMap.lcomp R R (Finsupp.lapply j) ∘ₗ B

/-- The contraction derivation sends a generator `ι x` to the scalar `B(h, x_j)`. -/
@[simp]
theorem fockContraction_ι (j : ℕ) (h : H) (x : ℕ →₀ H) :
    fockContraction B j h (ι R (ℕ →₀ H) x) = algebraMap R F (B h (x j)) := by
  simp [fockContraction]

/-- The contraction derivation on the generator `ι (single i k)`, which represents `k(-(i + 1))`:
the scalar `B(h, k)` if `i = j`, and zero otherwise. -/
theorem fockContraction_ι_single (i j : ℕ) (h k : H) :
    fockContraction B j h (ι R (ℕ →₀ H) (Finsupp.single i k)) =
      algebraMap R F (if i = j then B h k else 0) := by
  rw [fockContraction_ι, Finsupp.single_apply]
  split_ifs <;> simp

/-- The annihilation operator of the positive mode `h(j + 1)`: `(j + 1)` times the contraction
derivation `fockContraction B j h`. -/
def fockAnnihilation (j : ℕ) : H →ₗ[R] Module.End R F where
  toFun h := ((j : R) + 1) • (fockContraction B j h : F →ₗ[R] F)
  map_add' h k := LinearMap.ext fun v => by simp [smul_add]
  map_smul' r h := LinearMap.ext fun v => by simp [smul_comm r]

/-- The annihilation operator of `h(j + 1)` is `(j + 1)` times a contraction. -/
theorem fockAnnihilation_apply (j : ℕ) (h : H) :
    fockAnnihilation B j h = ((j : R) + 1) • (fockContraction B j h : F →ₗ[R] F) :=
  (rfl)

/-- The operator by which the mode `h(n)` of the Heisenberg algebra acts on the Fock space: the
creation operator `fockCreation j` for `n = -(j + 1)`, zero for `n = 0`, and the annihilation
operator `fockAnnihilation B j` for `n = j + 1`. -/
def fockMode : ℤ → H →ₗ[R] Module.End R F
  | .ofNat 0 => 0
  | .ofNat (j + 1) => fockAnnihilation B j
  | .negSucc j => fockCreation j

/-- The zero modes act by zero. -/
@[simp]
theorem fockMode_zero : fockMode B 0 = 0 :=
  (rfl)

/-- The positive mode `h(j + 1)` acts by the annihilation operator `fockAnnihilation B j h`. -/
@[simp]
theorem fockMode_natCast_add_one (j : ℕ) : fockMode B ((j : ℤ) + 1) = fockAnnihilation B j :=
  (rfl)

/-- The negative mode `h(-(j + 1))` acts by the creation operator `fockCreation j h`. -/
@[simp]
theorem fockMode_negSucc (j : ℕ) : fockMode B (Int.negSucc j) = fockCreation j :=
  (rfl)

/-- The creation operator is left multiplication by its generator. -/
theorem fockCreation_eq_mulLeft (j : ℕ) (h : H) :
    fockCreation (R := R) j h = LinearMap.mulLeft R (ι R (ℕ →₀ H) (Finsupp.single j h)) :=
  (rfl)

/-- Creation operators commute. -/
theorem lie_fockCreation_fockCreation (i j : ℕ) (h k : H) :
    ⁅fockCreation (R := R) i h, fockCreation (R := R) j k⁆ = 0 :=
  LinearMap.ext fun v => by
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, fockCreation_apply,
      mul_left_comm, sub_self, LinearMap.zero_apply]

/-- A contraction and a creation operator commute to the scalar `B(h, k) δ_{ij}`. -/
theorem lie_fockContraction_fockCreation (i j : ℕ) (h k : H) :
    ⁅(fockContraction B j h : Module.End R F), fockCreation (R := R) i k⁆ =
      (if i = j then B h k else 0) • 1 := by
  rw [fockCreation_eq_mulLeft, Derivation.lie_mulLeft, fockContraction_ι_single]
  exact LinearMap.ext fun v => by
    rw [LinearMap.mulLeft_apply, ← Algebra.smul_def, LinearMap.smul_apply, one_apply_eq_self]

/-- Contractions commute: their commutator is a derivation vanishing on the generators. -/
theorem lie_fockContraction_fockContraction (i j : ℕ) (h k : H) :
    ⁅(fockContraction B i h : Module.End R F), (fockContraction B j k : Module.End R F)⁆ = 0 := by
  rw [← Derivation.commutator_coe_linear_map]
  have : ⁅fockContraction B i h, fockContraction B j k⁆ = 0 :=
    derivation_ext fun x => by
      simp only [Derivation.commutator_apply, fockContraction_ι, Derivation.map_algebraMap,
        sub_self, zero_apply]
  rw [this]
  rfl

/-- The three shapes of a mode index: zero, positive, negative. -/
private theorem trichotomy_fockMode (n : ℤ) :
    n = 0 ∨ (∃ j : ℕ, n = (j : ℤ) + 1) ∨ ∃ j : ℕ, n = Int.negSucc j := by
  rcases n with (_ | j) | j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨j, rfl⟩)

/-- The **commutators of the mode operators** on the Fock space:
`⁅h(m), k(n)⁆ = m B(h, k) δ_{m + n, 0}`, the Heisenberg relations with `K` acting by `1`. -/
theorem lie_fockMode_fockMode (hB : B.IsSymm) (m n : ℤ) (h k : H) :
    ⁅fockMode B m h, fockMode B n k⁆ = (if m + n = 0 then (m : R) * B h k else 0) • 1 := by
  rcases trichotomy_fockMode m with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases trichotomy_fockMode n with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    simp only [fockMode_zero, fockMode_natCast_add_one,
      fockMode_negSucc, LinearMap.zero_apply, zero_lie, lie_zero, fockAnnihilation_apply, smul_lie,
      lie_smul, lie_fockContraction_fockContraction, lie_fockCreation_fockCreation, smul_zero,
      Int.cast_zero, zero_mul, ite_self, zero_smul]
  · split_ifs with hc <;> first | omega | simp
  · split_ifs with hc <;> first | omega | simp
  · rw [lie_fockContraction_fockCreation, smul_smul]
    by_cases hji : j = i
    · subst hji
      simp [Int.negSucc_eq]
    · split_ifs with hc <;> first | omega | simp
  · split_ifs with hc <;> first | omega | simp
  · rw [← lie_skew, lie_fockContraction_fockCreation, smul_neg, smul_smul]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left (by omega), Int.cast_negSucc, hB.eq k h, ← neg_smul, neg_mul]
      push_cast
      rfl
    · split_ifs with hc <;> first | omega | simp
  · split_ifs with hc <;> first | omega | simp

end Operators

section Representation

variable {R H : Type*} [CommRing R] [HasUniqueDiv R] [LieRing H] [LieAlgebra R H] [IsLieAbelian H]
  (B : LinearMap.BilinForm R H) (hB : B.IsSymm)

local notation "F" => SymmetricAlgebra R (ℕ →₀ H)

/-- The linear map underlying the Fock representation: a loop `p` acts by the sum of the mode
operators of its coefficients, and the central coordinate acts by scalars. -/
private def fockLinearMap : loopHeisenberg B hB →ₗ[R] Module.End R F :=
  ((Finsupp.lsum ℕ (fockMode B) ∘ₗ (toFinsupp R ℤ H).toLinearMap).coprod
      (LinearMap.toSpanSingleton R _ 1 ∘ₗ
        (TrivialLieModule.equiv R (loopAlgebra R ℤ H) R).toLinearMap)) ∘ₗ
    (ofProdLinearEquiv (heisenbergCocycle B hB)).symm.toLinearMap

private theorem fockLinearMap_heisenbergMode (n : ℤ) (h : H) :
    fockLinearMap B hB (heisenbergMode B hB n h) = fockMode B n h := by
  simp only [fockLinearMap, heisenbergMode_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coe_ofProdLinearEquiv_symm, Equiv.symm_apply_apply, LinearMap.coprod_apply,
    toFinsupp_single_tmul, Finsupp.lsum_single, map_zero, add_zero]

private theorem fockLinearMap_centralElement :
    fockLinearMap B hB (ofTwoCocycle.centralElement (heisenbergCocycle B hB)) = 1 := by
  simp [fockLinearMap]

/-- The **Fock representation** of the Heisenberg Lie algebra: the mode `h(n)` acts by
`fockMode B n h` and the central element `K` acts by the identity. -/
def fockRepresentation : loopHeisenberg B hB →ₗ⁅R⁆ Module.End R F :=
  { fockLinearMap B hB with
    map_lie' := fun {x y} => by
      -- The underlying function of the structure update is `fockLinearMap B hB` itself.
      change fockLinearMap B hB ⁅x, y⁆ = ⁅fockLinearMap B hB x, fockLinearMap B hB y⁆
      induction x using loopHeisenberg.induction_on B hB with
      | add x x' hx hx' => rw [add_lie, map_add, hx, hx', map_add, add_lie]
      | central r =>
        rw [smul_lie, ofTwoCocycle.centralElement_lie, smul_zero, map_zero, map_smul,
          fockLinearMap_centralElement, smul_lie, Ring.lie_def, one_mul, mul_one, sub_self,
          smul_zero]
      | mode m h =>
        induction y using loopHeisenberg.induction_on B hB with
        | add y y' hy hy' => rw [lie_add, map_add, hy, hy', map_add, lie_add]
        | central r =>
          rw [lie_smul, ofTwoCocycle.lie_centralElement, smul_zero, map_zero,
            map_smul, fockLinearMap_centralElement, lie_smul, Ring.lie_def, one_mul, mul_one,
            sub_self, smul_zero]
        | mode n k =>
          rw [lie_heisenbergMode_heisenbergMode, map_smul, fockLinearMap_centralElement,
            fockLinearMap_heisenbergMode, fockLinearMap_heisenbergMode,
            lie_fockMode_fockMode B hB] }

/-- The mode `h(n)` acts on the Fock space by `fockMode B n h`. -/
@[simp]
theorem fockRepresentation_heisenbergMode (n : ℤ) (h : H) :
    fockRepresentation B hB (heisenbergMode B hB n h) = fockMode B n h :=
  fockLinearMap_heisenbergMode B hB n h

/-- The central element `K` acts on the Fock space by the identity. -/
@[simp]
theorem fockRepresentation_centralElement :
    fockRepresentation B hB (ofTwoCocycle.centralElement (heisenbergCocycle B hB)) = 1 :=
  fockLinearMap_centralElement B hB

/-- The Fock space as a Lie module over the Heisenberg Lie algebra. -/
instance instLieRingModuleFock : LieRingModule (loopHeisenberg B hB) F :=
  LieRingModule.compLieHom F (fockRepresentation B hB)

/-- The Fock space is a Lie module over the Heisenberg Lie algebra: the action is linear. -/
instance instLieModuleFock : LieModule R (loopHeisenberg B hB) F :=
  LieModule.compLieHom F (fockRepresentation B hB)

/-- The action of the Heisenberg algebra on the Fock space is the Fock representation. -/
theorem lie_fock_eq_fockRepresentation (x : loopHeisenberg B hB) (v : F) :
    ⁅x, v⁆ = fockRepresentation B hB x v :=
  (rfl)

/-- The mode `h(n)` acts on the Fock space by `fockMode B n h`. -/
@[simp]
theorem heisenbergMode_lie_fock (n : ℤ) (h : H) (v : F) :
    ⁅heisenbergMode B hB n h, v⁆ = fockMode B n h v := by
  rw [lie_fock_eq_fockRepresentation, fockRepresentation_heisenbergMode]

/-- The central element `K` acts on the Fock space by the identity. -/
@[simp]
theorem centralElement_lie_fock (v : F) :
    ⁅ofTwoCocycle.centralElement (heisenbergCocycle B hB), v⁆ = v := by
  rw [lie_fock_eq_fockRepresentation, fockRepresentation_centralElement, one_apply_eq_self]

/-- The negative mode `h(-(j + 1))` acts on the Fock space by multiplication by the generator
`ι (single j h)`. -/
theorem heisenbergMode_negSucc_lie_fock (j : ℕ) (h : H) (v : F) :
    ⁅heisenbergMode B hB (Int.negSucc j) h, v⁆ = ι R (ℕ →₀ H) (Finsupp.single j h) * v := by
  rw [heisenbergMode_lie_fock, fockMode_negSucc, fockCreation_apply]

/-- The nonnegative modes `h(n)`, `n ≥ 0`, kill the vacuum `1`. -/
theorem heisenbergMode_lie_one_of_nonneg {n : ℤ} (hn : 0 ≤ n) (h : H) :
    ⁅heisenbergMode B hB n h, (1 : F)⁆ = 0 := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [heisenbergMode_lie_fock]
  rcases j with _ | j
  · rfl
  · rw [Nat.cast_succ, fockMode_natCast_add_one, fockAnnihilation_apply,
      LinearMap.smul_apply, Derivation.coeFn_coe, Derivation.map_one_eq_zero, smul_zero]

/-- **The vacuum two-point function**: for positive `m` and `n`,
`h(n) k(-m) 1 = n B(h, k) δ_{n, m} 1`. -/
theorem heisenbergMode_lie_heisenbergMode_lie_one {m n : ℤ} (hm : 0 < m) (hn : 0 < n) (h k : H) :
    ⁅heisenbergMode B hB n h, ⁅heisenbergMode B hB (-m) k, (1 : F)⁆⁆ =
      (if n = m then (n : R) * B h k else 0) • (1 : F) := by
  obtain ⟨i, rfl⟩ := Int.eq_succ_of_zero_lt hm
  obtain ⟨j, rfl⟩ := Int.eq_succ_of_zero_lt hn
  rw [← Int.negSucc_eq, heisenbergMode_negSucc_lie_fock, mul_one, heisenbergMode_lie_fock,
    fockMode_natCast_add_one, fockAnnihilation_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    fockContraction_ι_single, Algebra.algebraMap_eq_smul_one, smul_smul]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [ite_eq_right hij, ite_eq_right (by omega), mul_zero]

/-- **The vacuum generates the Fock module**: the Lie submodule generated by `1` is everything.
Iterated negative modes applied to `1` produce all monomials of the symmetric algebra. -/
theorem lieSpan_one_fock :
    LieSubmodule.lieSpan R (loopHeisenberg B hB) {(1 : F)} = ⊤ := by
  set N := LieSubmodule.lieSpan R (loopHeisenberg B hB) {(1 : F)}
  have key (a : F) : ∀ v ∈ N, a * v ∈ N := by
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
      intro v hv
      rw [← Algebra.smul_def]
      exact N.smul_mem r hv
    | ι x =>
      intro v hv
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => rw [map_add, add_mul]; exact N.add_mem hx hy
      | single j h =>
        rw [← heisenbergMode_negSucc_lie_fock B hB]
        exact N.lie_mem hv
    | mul a b ha hb => intro v hv; rw [mul_assoc]; exact ha _ (hb v hv)
    | add a b ha hb => intro v hv; rw [add_mul]; exact N.add_mem (ha v hv) (hb v hv)
  refine eq_top_iff.2 fun v _ => ?_
  rw [← mul_one v]
  exact key v 1 (LieSubmodule.subset_lieSpan rfl)

end Representation

section Translation

variable (R H : Type*) [CommRing R] [AddCommGroup H] [Module R H]

local notation "F" => SymmetricAlgebra R (ℕ →₀ H)

/-- The **translation operator** `T` of the Fock space: the derivation with
`T(h(-(j + 1))) = (j + 1) h(-(j + 2))` on the generators, that is
`T (ι (single j h)) = (j + 1) • ι (single (j + 1) h)`. -/
def fockTranslation : Derivation R F F :=
  mkDerivation (ι R (ℕ →₀ H) ∘ₗ Finsupp.lsum ℕ fun j => ((j : R) + 1) • Finsupp.lsingle (j + 1))

variable {R H}

/-- The translation operator on the generator representing `h(-(j + 1))`. -/
@[simp]
theorem fockTranslation_ι_single (j : ℕ) (h : H) :
    fockTranslation R H (ι R (ℕ →₀ H) (Finsupp.single j h)) =
      ((j : R) + 1) • ι R (ℕ →₀ H) (Finsupp.single (j + 1) h) := by
  rw [fockTranslation, mkDerivation_ι, LinearMap.comp_apply, Finsupp.lsum_single,
    LinearMap.smul_apply, Finsupp.lsingle_apply, map_smul]

/-- The translation operator kills the vacuum. -/
theorem fockTranslation_one : fockTranslation R H 1 = 0 :=
  (fockTranslation R H).map_one_eq_zero

variable (B : LinearMap.BilinForm R H)

/-- Translation commutes with the contraction at index zero. -/
theorem lie_fockTranslation_fockContraction_zero (h : H) :
    ⁅fockTranslation R H, fockContraction B 0 h⁆ = 0 :=
  derivation_ext fun x => by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | single i k => simp [Derivation.commutator_apply, Finsupp.single_apply]

/-- Translation lowers the index of a contraction: `⁅T, D_{j + 1}^h⁆ = -(j + 1) D_j^h`. -/
theorem lie_fockTranslation_fockContraction_succ (j : ℕ) (h : H) :
    ⁅fockTranslation R H, fockContraction B (j + 1) h⁆ = -((j : R) + 1) • fockContraction B j h :=
  derivation_ext fun x => by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | single i k =>
      simp only [Derivation.commutator_apply, fockContraction_ι, Derivation.map_algebraMap,
        fockTranslation_ι_single, Derivation.map_smul, zero_sub, smul_apply,
        Finsupp.single_apply, add_left_inj]
      split_ifs with hij
      · rw [hij, neg_smul]
      · simp

/-- **Translation covariance** of the mode operators: `⁅T, h(n)⁆ = -n h(n - 1)`. -/
theorem lie_fockTranslation_fockMode (n : ℤ) (h : H) :
    ⁅(fockTranslation R H : Module.End R F), fockMode B n h⁆ =
      -(n : R) • fockMode B (n - 1) h := by
  rcases trichotomy_fockMode n with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp
  · rw [fockMode_natCast_add_one, fockAnnihilation_apply, lie_smul,
      ← Derivation.commutator_coe_linear_map, add_sub_cancel_right]
    rcases j with _ | j
    · simp [lie_fockTranslation_fockContraction_zero]
    · simp only [lie_fockTranslation_fockContraction_succ, Nat.cast_add, Nat.cast_one,
        fockMode_natCast_add_one, fockAnnihilation_apply]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.smul_apply, Derivation.coeFn_coe, smul_apply, smul_smul]
      push_cast
      congr 1
      ring
  · rw [show Int.negSucc j - 1 = Int.negSucc (j + 1) by omega, fockMode_negSucc, fockMode_negSucc,
      fockCreation_eq_mulLeft, fockCreation_eq_mulLeft, Derivation.lie_mulLeft,
      fockTranslation_ι_single, Int.cast_negSucc, neg_neg]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply, smul_mul_assoc]
    push_cast
    rfl

end Translation

end TauCeti
