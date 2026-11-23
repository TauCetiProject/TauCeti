/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Center
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Massey.DefiningSystem
import TauCeti.Data.Fin.Basic
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Dwyer's criteria for Massey products

Let `Γ` be a topological group, `R` a discrete ring with trivial `Γ`-action, `n ≥ 2`, and
`χ 0, …, χ (n - 1) : Γ → R`. Write `Uₙ₊₁(R)` for the upper-unitriangular group with rows and
columns indexed by `0, …, n`, and `Z` for its centre, the corner subgroup `{e₀ₙ(t)}`
(`TauCeti.UpperUnitriangularGroup.center_eq_superdiagonalSubgroup`).

The defining equations of a defining system say exactly that the matrix with these entries off
the diagonal multiplies like a homomorphism, away from the corner. Since multiplying by `Z` changes
only the corner, this gives Dwyer's criteria:

* the Massey product of `χ` is defined exactly when there is a continuous homomorphism
  `Γ → Uₙ₊₁(R) / Z` whose adjacent entries are the `χ i`
  (`TauCeti.ContCohomology.masseyDefined_iff_exists_lift`);
* it contains zero exactly when there is a continuous homomorphism `Γ → Uₙ₊₁(R)` whose adjacent
  entries are the `χ i` (`TauCeti.ContCohomology.masseyContainsZero_iff_exists_lift`). The corner
  entry of such a lift is a primitive of the value of the defining system formed by its other
  entries.

The two directions of the first criterion are the homomorphism
`TauCeti.ContCohomology.DefiningSystem.toQuotientLift` attached to a defining system, characterized
by `TauCeti.ContCohomology.DefiningSystem.mk_eq_toQuotientLift_iff`, and the defining system
`TauCeti.ContCohomology.DefiningSystem.ofLift` formed by the entries of a lift. The lift of the
second criterion is the homomorphism `TauCeti.ContCohomology.DefiningSystem.toLift` attached to a
defining system and a primitive of its value, whose corner entry is the primitive.

Continuity of a homomorphism into the discrete groups `Uₙ₊₁(R)` and `Uₙ₊₁(R) / Z` is written as
openness of its kernel. Neither criterion assumes that the `χ i` are homomorphisms, nor that the
lifts are surjective.

## References

* W. G. Dwyer, *Homology, Massey products and maps between groups*, J. Pure Appl. Algebra 6
  (1975), Theorem 2.4 (with the opposite sign convention for the value).
* Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*, Duke Math. J.
  172 (2023), Proposition 2.2 and Corollary 2.3.
-/

public section

open Matrix

namespace TauCeti.ContCohomology

open UpperUnitriangularGroup

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {R : Type*} [Ring R] [TopologicalSpace R]
  {n : ℕ} {χ : Fin n → Γ → R}

/-! ### From defining systems to matrices -/

/-- The matrix whose diagonal entries are `1`, whose corner entry is `c g` and whose other entries
are the entries of the defining system `D` at `g`. -/
private def liftEntries (D : DefiningSystem Γ R n χ) (c : Γ → R) (g : Γ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j ↦ if i = j then 1 else if i = 0 ∧ j = Fin.last n then c g else D.entry i j g

private theorem liftEntries_apply_of_ne (D : DefiningSystem Γ R n χ) (c : Γ → R) (g : Γ)
    {i j : Fin (n + 1)} (hij : i ≠ j) (hc : ¬ (i = 0 ∧ j = Fin.last n)) :
    liftEntries D c g i j = D.entry i j g := by
  simp only [liftEntries, of_apply, ite_eq_right hij, ite_eq_right hc]

private theorem liftEntries_apply_of_corner (D : DefiningSystem Γ R n χ) (c : Γ → R) (g : Γ)
    {i j : Fin (n + 1)} (hij : i ≠ j) (hc : i = 0 ∧ j = Fin.last n) :
    liftEntries D c g i j = c g := by
  simp only [liftEntries, of_apply, ite_eq_right hij, ite_eq_left hc]

private theorem isUpperUnitriangular_liftEntries (D : DefiningSystem Γ R n χ) (c : Γ → R)
    (g : Γ) : (liftEntries D c g).IsUpperUnitriangular := by
  rw [isUpperUnitriangular_iff]
  refine ⟨fun i j hji ↦ ?_, fun i ↦ by simp [liftEntries]⟩
  have hc : ¬ (i = 0 ∧ j = Fin.last n) := fun h ↦ absurd hji (by rw [h.1]; exact Fin.not_lt_zero j)
  rw [liftEntries_apply_of_ne D c g hji.ne' hc, D.entry_eq_zero i j (Or.inl hji.le), Pi.zero_apply]

/-- The indices strictly between `i` and `j` pair with neither `i` nor `j` to form the corner. -/
private theorem not_corner_of_mem_Ioo {i j k : Fin (n + 1)} (hk : k ∈ Finset.Ioo i j) :
    ¬ (i = 0 ∧ k = Fin.last n) ∧ ¬ (k = 0 ∧ j = Fin.last n) := by
  rw [Finset.mem_Ioo] at hk
  exact ⟨fun h ↦ absurd hk.2 (by rw [h.2]; exact not_lt.2 (Fin.le_last j)),
    fun h ↦ absurd hk.1 (by rw [h.1]; exact Fin.not_lt_zero i)⟩

/-- An entry strictly above the diagonal of a product of two matrices `liftEntries`: by the
defining equations it is the entry at the product away from the corner, while at the corner it is
the sum of the two corner entries minus the value of `D`. -/
private theorem liftEntries_mul_apply (D : DefiningSystem Γ R n χ) (c : Γ → R) (g h : Γ)
    {i j : Fin (n + 1)} (hij : i < j) :
    (liftEntries D c g * liftEntries D c h) i j =
      if i = 0 ∧ j = Fin.last n then c g + c h - D.value (g, h) else D.entry i j (g * h) := by
  rw [(isUpperUnitriangular_liftEntries D c g).mul_apply_of_lt
    (isUpperUnitriangular_liftEntries D c h) hij]
  -- The intermediate entries are never at the corner.
  have hsum : ∑ k ∈ Finset.Ioo i j, liftEntries D c g i k * liftEntries D c h k j =
      ∑ k ∈ Finset.Ioo i j, D.entry i k g * D.entry k j h := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    obtain ⟨h1, h2⟩ := not_corner_of_mem_Ioo hk
    rw [Finset.mem_Ioo] at hk
    rw [liftEntries_apply_of_ne D c g hk.1.ne h1, liftEntries_apply_of_ne D c h hk.2.ne h2]
  rw [hsum]
  by_cases hc : i = 0 ∧ j = Fin.last n
  · rw [ite_eq_left hc, liftEntries_apply_of_corner D c g hij.ne hc,
      liftEntries_apply_of_corner D c h hij.ne hc, DefiningSystem.value_apply]
    obtain ⟨rfl, rfl⟩ := hc
    abel
  · rw [ite_eq_right hc, liftEntries_apply_of_ne D c g hij.ne hc,
      liftEntries_apply_of_ne D c h hij.ne hc, D.entry_mul i j hij hc]

private theorem continuous_liftEntries_apply (D : DefiningSystem Γ R n χ) {c : Γ → R}
    (hc : Continuous c) (i j : Fin (n + 1)) : Continuous fun g ↦ liftEntries D c g i j := by
  by_cases hij : i = j
  · simp only [liftEntries, of_apply, ite_eq_left hij]
    exact continuous_const
  by_cases hcorner : i = 0 ∧ j = Fin.last n
  · simpa only [liftEntries_apply_of_corner D c _ hij hcorner] using hc
  · simpa only [liftEntries_apply_of_ne D c _ hij hcorner] using D.continuous_entry i j

/-- For a continuous corner `c`, the matrices `liftEntries D c g` depend continuously on `g`; for
a discrete `R` their space is discrete, so the set of `g` where they lie in a given set is open. -/
private theorem continuous_liftEntries (D : DefiningSystem Γ R n χ) {c : Γ → R}
    (hc : Continuous c) : Continuous fun g ↦ (liftEntries D c g : Fin (n + 1) → Fin (n + 1) → R) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_liftEntries_apply D hc i j

/-- The matrix `liftEntries D c g` as an element of `Uₙ₊₁(R)`. -/
private noncomputable def liftMatrix (D : DefiningSystem Γ R n χ) (c : Γ → R) (g : Γ) :
    upperUnitriangularGroup (Fin (n + 1)) R :=
  ⟨(isUpperUnitriangular_liftEntries D c g).toGL,
    toGL_mem_upperUnitriangularGroup (isUpperUnitriangular_liftEntries D c g)⟩

private theorem coe_liftMatrix (D : DefiningSystem Γ R n χ) (c : Γ → R) (g : Γ) :
    ((liftMatrix D c g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      liftEntries D c g :=
  IsUpperUnitriangular.coe_toGL _

/-- The adjacent entries of `liftEntries D c g` are the inputs at `g`. -/
private theorem liftMatrix_apply_castSucc_succ (D : DefiningSystem Γ R n χ) (hn : 2 ≤ n)
    (c : Γ → R) (g : Γ) (i : Fin n) :
    ((liftMatrix D c g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
      i.castSucc i.succ = χ i g := by
  rw [coe_liftMatrix, liftEntries_apply_of_ne D c g (Fin.castSucc_lt_succ (i := i)).ne
    (Fin.not_castSucc_eq_zero_and_succ_eq_last hn i), D.entry_castSucc_succ]

/-! ### From lifts to defining systems -/

omit [Group Γ] in
/-- The defining system formed by the entries away from the diagonal and the corner of a family
`L g` of upper-unitriangular matrices, whose entries are continuous, which multiply like a
homomorphism away from the corner, and whose adjacent entries are the inputs. Its entries are
described by `TauCeti.ContCohomology.DefiningSystem.ofLift_entry`. -/
def DefiningSystem.ofLift [Mul Γ] (hn : 2 ≤ n) (L : Γ → upperUnitriangularGroup (Fin (n + 1)) R)
    (hcont : ∀ i j, Continuous fun g ↦
      ((L g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j)
    (hmul : ∀ g h : Γ, ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) →
      ((L (g * h) : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
        (((L g * L h : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j)
    (hχ : ∀ (g : Γ) (i : Fin n),
      ((L g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ =
        χ i g) :
    DefiningSystem Γ R n χ where
  entry i j g := if i < j ∧ ¬ (i = 0 ∧ j = Fin.last n) then
    ((L g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j else 0
  continuous_entry i j := by
    by_cases hij : i < j ∧ ¬ (i = 0 ∧ j = Fin.last n)
    · simpa only [ite_eq_left hij] using hcont i j
    · simpa only [ite_eq_right hij] using continuous_const
  entry_castSucc_succ i := by
    funext g
    rw [ite_eq_left ⟨Fin.castSucc_lt_succ, Fin.not_castSucc_eq_zero_and_succ_eq_last hn i⟩, hχ]
  entry_mul i j hij hc g h := by
    rw [ite_eq_left ⟨hij, hc⟩, ite_eq_left ⟨hij, hc⟩, ite_eq_left ⟨hij, hc⟩, hmul g h i j hij hc,
      UpperUnitriangularGroup.mul_apply_of_lt (L g) (L h) hij]
    refine congrArg _ (Finset.sum_congr rfl fun k hk ↦ ?_)
    obtain ⟨h1, h2⟩ := not_corner_of_mem_Ioo hk
    rw [Finset.mem_Ioo] at hk
    rw [ite_eq_left ⟨hk.1, h1⟩, ite_eq_left ⟨hk.2, h2⟩]
  entry_eq_zero i j h := by
    refine funext fun g ↦ ite_eq_right ?_
    rintro ⟨hij, hc⟩
    rcases h with h | ⟨h0, hl, _⟩
    · exact absurd hij (not_lt.2 h)
    · exact hc ⟨h0, hl⟩

omit [Group Γ] in
/-- The entries of `DefiningSystem.ofLift` strictly above the diagonal and away from the corner
are those of the lift. -/
theorem DefiningSystem.ofLift_entry [Mul Γ] (hn : 2 ≤ n)
    (L : Γ → upperUnitriangularGroup (Fin (n + 1)) R) (hcont hmul hχ) {i j : Fin (n + 1)}
    (hij : i < j) (hc : ¬ (i = 0 ∧ j = Fin.last n)) (g : Γ) :
    (DefiningSystem.ofLift (χ := χ) hn L hcont hmul hχ).entry i j g =
      ((L g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j :=
  ite_eq_left ⟨hij, hc⟩

/-- The defining system formed by the entries of a homomorphism `β : Γ → Uₙ₊₁(R)` with continuous
entries. -/
private def definingSystemOfMonoidHom (hn : 2 ≤ n)
    (β : Γ →* upperUnitriangularGroup (Fin (n + 1)) R)
    (hcont : ∀ i j, Continuous fun g ↦
      ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j)
    (hχ : ∀ (g : Γ) (i : Fin n),
      ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ =
        χ i g) :
    DefiningSystem Γ R n χ :=
  DefiningSystem.ofLift hn β hcont (fun g h _ _ _ _ ↦ by rw [map_mul]) hχ

private theorem definingSystemOfMonoidHom_entry (hn : 2 ≤ n)
    (β : Γ →* upperUnitriangularGroup (Fin (n + 1)) R) (hcont hχ) {i j : Fin (n + 1)}
    (hij : i < j) (hc : ¬ (i = 0 ∧ j = Fin.last n)) (g : Γ) :
    (definingSystemOfMonoidHom (χ := χ) hn β hcont hχ).entry i j g =
      ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j :=
  DefiningSystem.ofLift_entry hn β _ _ _ hij hc g

/-! ### Lifts attached to a defining system -/

/-- The homomorphism `Γ → Uₙ₊₁(R) / Z` attached to a defining system `D`: it sends `g` to the
class modulo the centre of any upper-unitriangular matrix whose entries away from the diagonal and
the corner are those of `D` at `g`
(`TauCeti.ContCohomology.DefiningSystem.mk_eq_toQuotientLift_iff`). -/
noncomputable def DefiningSystem.toQuotientLift (D : DefiningSystem Γ R n χ) :
    Γ →* upperUnitriangularGroup (Fin (n + 1)) R ⧸
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) :=
  MonoidHom.mk' (fun g ↦ (liftMatrix D 0 g : _ ⧸ _)) fun g h ↦ by
    rw [← QuotientGroup.mk_mul, mk_eq_mk_iff]
    intro i j hij hc
    rw [UpperUnitriangularGroup.coe_mul, coe_liftMatrix, coe_liftMatrix, coe_liftMatrix,
      liftEntries_mul_apply D 0 g h hij, ite_eq_right hc, liftEntries_apply_of_ne D 0 _ hij.ne hc]

private theorem toQuotientLift_apply (D : DefiningSystem Γ R n χ) (g : Γ) :
    D.toQuotientLift g = QuotientGroup.mk (liftMatrix D 0 g) := by
  rw [DefiningSystem.toQuotientLift, MonoidHom.mk'_apply]

/-- An element `u` of `Uₙ₊₁(R)` represents `D.toQuotientLift g` exactly when its entries
strictly above the diagonal and away from the corner are those of `D` at `g`. -/
theorem DefiningSystem.mk_eq_toQuotientLift_iff (D : DefiningSystem Γ R n χ) (g : Γ)
    {u : upperUnitriangularGroup (Fin (n + 1)) R} :
    (QuotientGroup.mk u : upperUnitriangularGroup (Fin (n + 1)) R ⧸
        Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) = D.toQuotientLift g ↔
      ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) →
        ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j = D.entry i j g := by
  rw [toQuotientLift_apply, mk_eq_mk_iff]
  refine forall₄_congr fun i j hij hc ↦ ?_
  rw [coe_liftMatrix, liftEntries_apply_of_ne D 0 g hij.ne hc]

/-- For a discrete `R`, the homomorphism `D.toQuotientLift` is continuous: its kernel is open. -/
theorem DefiningSystem.isOpen_ker_toQuotientLift [DiscreteTopology R]
    (D : DefiningSystem Γ R n χ) : IsOpen (D.toQuotientLift.ker : Set Γ) := by
  have hker : (D.toQuotientLift.ker : Set Γ) = {g | ∀ i j, (i < j ∧ ¬ (i = 0 ∧ j = Fin.last n)) →
      liftEntries D 0 g i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j} := by
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, toQuotientLift_apply, ← QuotientGroup.mk_one,
      mk_eq_mk_iff, Set.mem_ofPred_eq]
    simp only [coe_liftMatrix, OneMemClass.coe_one, Units.val_one, and_imp]
  rw [hker]
  exact (isOpen_discrete {M : Fin (n + 1) → Fin (n + 1) → R | ∀ i j,
    (i < j ∧ ¬ (i = 0 ∧ j = Fin.last n)) →
      M i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j}).preimage
    (continuous_liftEntries D continuous_const)

/-- The homomorphism `Γ → Uₙ₊₁(R)` attached to a defining system `D` and a primitive `f` of its
value: it sends `g` to the upper-unitriangular matrix whose corner entry is `f g` and whose other
entries above the diagonal are those of `D` at `g`
(`TauCeti.ContCohomology.DefiningSystem.toLift_apply_zero_last`,
`TauCeti.ContCohomology.DefiningSystem.toLift_apply_of_ne`). -/
noncomputable def DefiningSystem.toLift (D : DefiningSystem Γ R n χ) (f : Γ → R)
    (hval : ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g) :
    Γ →* upperUnitriangularGroup (Fin (n + 1)) R :=
  MonoidHom.mk' (liftMatrix D f) fun g h ↦ by
    refine ext fun i j hij ↦ ?_
    rw [UpperUnitriangularGroup.coe_mul, coe_liftMatrix, coe_liftMatrix, coe_liftMatrix,
      liftEntries_mul_apply D f g h hij]
    by_cases hc : i = 0 ∧ j = Fin.last n
    · rw [ite_eq_left hc, liftEntries_apply_of_corner D f _ hij.ne hc, hval g h]
      abel
    · rw [ite_eq_right hc, liftEntries_apply_of_ne D f _ hij.ne hc]

private theorem toLift_apply (D : DefiningSystem Γ R n χ) (f : Γ → R)
    (hval : ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g) (g : Γ) :
    D.toLift f hval g = liftMatrix D f g := by
  rw [DefiningSystem.toLift, MonoidHom.mk'_apply]

/-- The corner entry of `D.toLift f hval g` is `f g`. -/
@[simp]
theorem DefiningSystem.toLift_apply_zero_last [NeZero n] (D : DefiningSystem Γ R n χ)
    (f : Γ → R) (hval : ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g) (g : Γ) :
    ((D.toLift f hval g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0
      (Fin.last n) = f g := by
  rw [toLift_apply, coe_liftMatrix, liftEntries_apply_of_corner D f g Fin.last_pos'.ne ⟨rfl, rfl⟩]

/-- Away from the diagonal and the corner, the entries of `D.toLift f hval g` are those of `D` at
`g`. -/
theorem DefiningSystem.toLift_apply_of_ne (D : DefiningSystem Γ R n χ) (f : Γ → R)
    (hval : ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g) (g : Γ) {i j : Fin (n + 1)}
    (hij : i ≠ j) (hc : ¬ (i = 0 ∧ j = Fin.last n)) :
    ((D.toLift f hval g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
      D.entry i j g := by
  rw [toLift_apply, coe_liftMatrix, liftEntries_apply_of_ne D f g hij hc]

/-- For a discrete `R` and a continuous primitive `f`, the homomorphism `D.toLift f hval` is
continuous: its kernel is open. -/
theorem DefiningSystem.isOpen_ker_toLift [DiscreteTopology R] (D : DefiningSystem Γ R n χ)
    {f : Γ → R} (hf : Continuous f) (hval : ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g) :
    IsOpen ((D.toLift f hval).ker : Set Γ) := by
  have hker : ((D.toLift f hval).ker : Set Γ) = {g | ∀ i j, i < j →
      liftEntries D f g i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j} := by
    ext g
    rw [SetLike.mem_coe, MonoidHom.mem_ker, toLift_apply, Set.mem_ofPred_eq]
    refine ⟨fun h i j _ ↦ ?_, fun h ↦ ext fun i j hij ↦ ?_⟩
    · rw [← coe_liftMatrix D f g, h, OneMemClass.coe_one, Units.val_one]
    · rw [coe_liftMatrix, h i j hij, OneMemClass.coe_one, Units.val_one]
  rw [hker]
  exact (isOpen_discrete {M : Fin (n + 1) → Fin (n + 1) → R | ∀ i j, i < j →
    M i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j}).preimage (continuous_liftEntries D hf)

/-! ### Defining systems attached to lifts -/

/-- The entries of a homomorphism with open kernel are continuous. -/
private theorem continuous_apply_of_isOpen_ker [SeparatelyContinuousMul Γ]
    {β : Γ →* upperUnitriangularGroup (Fin (n + 1)) R} (hβ : IsOpen (β.ker : Set Γ))
    (i j : Fin (n + 1)) :
    Continuous fun g ↦ ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j :=
  ((β.isLocallyConstant_of_isOpen_ker hβ).comp fun u ↦
    ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j).continuous

/-- The value of the defining system formed by the entries of a lift `β : Γ → Uₙ₊₁(R)` is the
coboundary of its corner entry. -/
private theorem value_definingSystemOfMonoidHom (hn : 2 ≤ n)
    (β : Γ →* upperUnitriangularGroup (Fin (n + 1)) R) (hcont hχ) (g h : Γ) :
    (definingSystemOfMonoidHom (χ := χ) hn β hcont hχ).value (g, h) =
      ((β h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) -
        ((β (g * h) : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0
          (Fin.last n) +
        ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) := by
  have : NeZero n := ⟨by omega⟩
  rw [map_mul, UpperUnitriangularGroup.mul_apply_of_lt (β g) (β h) Fin.last_pos',
    DefiningSystem.value_apply]
  -- The intermediate entries of the value are entries of the lift.
  have hsum : ∑ m ∈ Finset.Ioo (0 : Fin (n + 1)) (Fin.last n),
      (definingSystemOfMonoidHom (χ := χ) hn β hcont hχ).entry 0 m g *
        (definingSystemOfMonoidHom (χ := χ) hn β hcont hχ).entry m (Fin.last n) h =
        ∑ m ∈ Finset.Ioo (0 : Fin (n + 1)) (Fin.last n),
          ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 m *
            ((β h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) m
              (Fin.last n) := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    obtain ⟨h1, h2⟩ := not_corner_of_mem_Ioo hm
    rw [Finset.mem_Ioo] at hm
    rw [definingSystemOfMonoidHom_entry hn β _ _ hm.1 h1 g,
      definingSystemOfMonoidHom_entry hn β _ _ hm.2 h2 h]
  rw [hsum]
  abel

/-! ### Dwyer's criteria -/

/-- **Dwyer's criterion for definedness** (Dwyer, Theorem 2.4; Harpaz–Wittenberg, Proposition 2.2
and Corollary 2.3). Let `R` be a discrete ring with trivial action and `n ≥ 2`. The `n`-fold
Massey product of `χ` is defined exactly when there is a continuous homomorphism
`β : Γ → Uₙ₊₁(R) / Z`, `Z` the centre, whose adjacent entries are the `χ i`. The adjacent entries
of a class modulo `Z` are well defined (`TauCeti.UpperUnitriangularGroup.mk_eq_mk_iff`). -/
theorem masseyDefined_iff_exists_lift [SeparatelyContinuousMul Γ] [DiscreteTopology R]
    (hn : 2 ≤ n) (χ : Fin n → Γ → R) :
    MasseyDefined χ ↔
      ∃ β : Γ →* upperUnitriangularGroup (Fin (n + 1)) R ⧸
          Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R),
        IsOpen (β.ker : Set Γ) ∧
          ∀ g : Γ, ∃ u : upperUnitriangularGroup (Fin (n + 1)) R,
            (QuotientGroup.mk u : upperUnitriangularGroup (Fin (n + 1)) R ⧸
                Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) = β g ∧
              ∀ i : Fin n, ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
                i.castSucc i.succ = χ i g := by
  rw [masseyDefined_iff]
  refine ⟨fun ⟨D⟩ ↦ ⟨D.toQuotientLift, D.isOpen_ker_toQuotientLift,
    fun g ↦ ⟨liftMatrix D 0 g, (toQuotientLift_apply D g).symm,
      liftMatrix_apply_castSucc_succ D hn 0 g⟩⟩, ?_⟩
  -- Representatives of the classes `β g` have well-defined entries away from the corner.
  rintro ⟨β, hβ, hlift⟩
  refine ⟨DefiningSystem.ofLift hn (fun g ↦ (β g).out) (fun i j ↦ ?_) (fun g h i j hij hc ↦ ?_)
    (fun g i ↦ ?_)⟩
  · exact ((β.isLocallyConstant_of_isOpen_ker hβ).comp fun q ↦
      ((q.out : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) i j).continuous
  · refine mk_eq_mk_iff.1 ?_ i j hij hc
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
      QuotientGroup.out_eq', map_mul]
  · obtain ⟨u, hu, hχ⟩ := hlift g
    have hout : (QuotientGroup.mk (β g).out : upperUnitriangularGroup (Fin (n + 1)) R ⧸
        Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) = QuotientGroup.mk u := by
      rw [QuotientGroup.out_eq', hu]
    exact (mk_eq_mk_iff.1 hout _ _ Fin.castSucc_lt_succ
      (Fin.not_castSucc_eq_zero_and_succ_eq_last hn i)).trans (hχ i)

/-- **Dwyer's criterion for containing zero** (Dwyer, Theorem 2.4; Harpaz–Wittenberg,
Proposition 2.2 and Corollary 2.3). Let `R` be a discrete ring with trivial action and `n ≥ 2`.
The `n`-fold Massey product of `χ` contains zero exactly when there is a continuous homomorphism
`β : Γ → Uₙ₊₁(R)` whose adjacent entries are the `χ i`. No surjectivity is asked of `β`. -/
theorem masseyContainsZero_iff_exists_lift [SeparatelyContinuousMul Γ] [DiscreteTopology R]
    (hn : 2 ≤ n) (χ : Fin n → Γ → R) :
    MasseyContainsZero χ ↔
      ∃ β : Γ →* upperUnitriangularGroup (Fin (n + 1)) R,
        IsOpen (β.ker : Set Γ) ∧
          ∀ (g : Γ) (i : Fin n),
            ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
              i.castSucc i.succ = χ i g := by
  rw [masseyContainsZero_iff]
  refine ⟨fun ⟨D, f, hf, hval⟩ ↦ ⟨D.toLift f hval, D.isOpen_ker_toLift hf hval,
    fun g i ↦ by rw [toLift_apply]; exact liftMatrix_apply_castSucc_succ D hn f g i⟩,
    fun ⟨β, hβ, hχ⟩ ↦ ?_⟩
  -- The entries of a lift form a defining system, and its corner entry is a primitive.
  exact ⟨_, fun g ↦ ((β g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0
    (Fin.last n), continuous_apply_of_isOpen_ker hβ 0 (Fin.last n),
    value_definingSystemOfMonoidHom hn β (continuous_apply_of_isOpen_ker hβ) hχ⟩

end TauCeti.ContCohomology
