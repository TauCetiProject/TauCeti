/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount

/-!
# Splitting symbols of Galois sets and the transitive mass

Let `K` be a nonarchimedean local field with `q` residue classes. A labelled Galois set
`ρ : TauCeti.GaloisSet K n` is the set of `K`-embeddings of an étale algebra `∏ L_i` into
`SeparableClosure K`, and its orbits are the factors `L_i`: the fixed field of a point stabilizer
of an orbit is a copy of the corresponding factor. The *splitting symbol*
`TauCeti.GaloisSet.splittingSymbol ρ` is the multiset, over the orbits, of the pair `(f, e)` of
residue degree and ramification index of that fixed field [Bhargava 2007, (2.1)]. Conjugate
stabilizers have isomorphic fixed fields, so the pair does not depend on the point chosen in the
orbit. Its entries are pairs of positive integers with `∑ f e = n`, the size of the Galois set.

A Galois set of size `f * e` has splitting symbol `{(f, e)}` exactly when it is transitive and the
fixed field of a point stabilizer has residue degree `f`. The transitive bridge
`TauCeti.GaloisSet.tsum_isTransitive` turns the sum over these Galois sets into `(f e - 1)!` times
a sum over the subextensions of `SeparableClosure K` of degree `f e` and residue degree `f`, which
`TauCeti.tsum_inertiaDegree_eq` (Serre's mass formula over the unramified extension of degree `f`)
evaluates. The result is the **transitive mass**
`(1 / (f e)!) ∑_ρ q ^ (-d(ρ)) = 1 / (f q ^ (f (e - 1)))`, the building block from which the mass
of an arbitrary splitting type is assembled [Bhargava 2007, Prop. 2.1].

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set.
* `TauCeti.GaloisSet.mem_splittingSymbol`: its entries are the pairs `(f, e)` of the fixed fields
  of point stabilizers.
* `TauCeti.GaloisSet.sum_map_mul_splittingSymbol`: the degrees `f e` of the entries add up to `n`.
* `TauCeti.GaloisSet.splittingSymbol_eq_of_equiv`: invariance under equivariant relabelling.
* `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`: the symbol `{(f, e)}` characterizes the
  transitive Galois sets of size `f e` with residue degree `f`.
* `TauCeti.GaloisSet.tsum_splittingSymbol_eq_singleton`: these Galois sets weigh `(f e - 1)!` times
  the subextensions of degree `f e` and residue degree `f`.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: the transitive mass
  `1 / (f q ^ (f (e - 1)))`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel IntermediateField _root_.MulAction
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Action

variable {X : Type*} [MulAction Gal(SeparableClosure K/K) X]

/-- Translating a point does not change the residue degree of its stabilizer's fixed field, since
the two fixed fields are conjugate. -/
@[simp]
theorem inertiaDegree_fixedField_stabilizer_smul (σ : Gal(SeparableClosure K/K)) (x : X) :
    (fixedField (stabilizer Gal(SeparableClosure K/K) (σ • x))).inertiaDegree =
      (fixedField (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree := by
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (IntermediateField.inertiaDegree_eq_of_algEquiv
    ((fixedField (stabilizer Gal(SeparableClosure K/K) x)).equivMap σ.toAlgHom)).symm

end Action

namespace GaloisSet

variable {n : ℕ}

/-- The **splitting symbol** of a labelled Galois set [Bhargava 2007, (2.1)]: the multiset, over
its orbits, of the pair `(f, e)` of residue degree `f` and ramification index `e = [F : K] / f` of
the fixed field `F` of the stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  letI := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  Finset.univ.val.map fun ω : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ↦
    ((fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
      Module.finrank K (fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
        (fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)

/-- The splitting symbol is the image of the orbits, for any enumeration of them. -/
theorem splittingSymbol_eq_map (ρ : GaloisSet K n)
    [Fintype (letI := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))] :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      Finset.univ.val.map fun ω : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ↦
        ((fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
          Module.finrank K (fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
            (fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)) := by
  rw [splittingSymbol, Subsingleton.elim (Fintype.ofFinite _) ‹_›]

/-- The splitting symbol has one entry per orbit. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    ρ.splittingSymbol.card =
      (letI := ρ.mulAction; Nat.card (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Fintype.card_eq_nat_card]

/-- The entry of an orbit in the splitting symbol can be computed at any point of the orbit. -/
private theorem splittingSymbol_entry_out (ρ : GaloisSet K n)
    {ω : letI := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)} {x : Fin n}
    (hx : (letI := ρ.mulAction
      (Quotient.mk'' x : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = ω) :
    (letI := ρ.mulAction
    ((fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
      Module.finrank K (fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
        (fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)) =
      (letI := ρ.mulAction
      ((fixedField (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree,
        Module.finrank K (fixedField (stabilizer Gal(SeparableClosure K/K) x)) /
          (fixedField (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree)) := by
  let := ρ.mulAction
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  rw [inertiaDegree_fixedField_stabilizer_smul, ρ.finrank_fixedField_stabilizer,
    ρ.finrank_fixedField_stabilizer, orbit_smul]

/-- The entries of the splitting symbol are the pairs `(f, [F : K] / f)` of the fixed fields `F`
of point stabilizers, where `f` is the residue degree of `F`. -/
theorem mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ} :
    x ∈ ρ.splittingSymbol ↔ ∃ i : Fin n,
      (letI := ρ.mulAction
      ((fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree,
        Module.finrank K (fixedField (stabilizer Gal(SeparableClosure K/K) i)) /
          (fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree)) = x := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map, Multiset.mem_map]
  constructor
  · rintro ⟨ω, -, rfl⟩
    exact ⟨ω.out, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Quotient.mk'' i, Finset.mem_univ _, ρ.splittingSymbol_entry_out rfl⟩

/-- The entries of a splitting symbol are pairs of positive integers. -/
theorem pos_of_mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ}
    (hx : x ∈ ρ.splittingSymbol) : 0 < x.1 ∧ 0 < x.2 := by
  obtain ⟨i, rfl⟩ := ρ.mem_splittingSymbol.1 hx
  let := ρ.mulAction
  have := ρ.finiteDimensional_fixedField_stabilizer i
  have hf :=
    IntermediateField.inertiaDegree_pos (fixedField (stabilizer Gal(SeparableClosure K/K) i))
  have hd := inertiaDegree_dvd_finrank (fixedField (stabilizer Gal(SeparableClosure K/K) i))
  exact ⟨hf, Nat.div_pos (Nat.le_of_dvd Module.finrank_pos hd) hf⟩

/-- The degrees `f e` of the entries of the splitting symbol add up to the size of the Galois
set: the entry of an orbit has degree the size of that orbit. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map, Multiset.map_map, Finset.sum_map_val]
  simp_rw [Function.comp_apply,
    Nat.mul_div_cancel' (inertiaDegree_dvd_finrank _), ρ.finrank_fixedField_stabilizer]
  rw [← Nat.card_sigma, ← Nat.card_congr (selfEquivSigmaOrbits _ _), Nat.card_fin]

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n), e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  let := ρ.mulAction
  let := τ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E := MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol_eq_map, splittingSymbol_eq_map, ← Multiset.map_univ_val_equiv E,
    Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ ↦ ?_
  rw [Function.comp_apply, τ.splittingSymbol_entry_out (x := e ω.out)
    (by rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']),
    MulAction.stabilizer_eq_of_injective e e.injective he]

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The splitting symbol of a transitive Galois set has the single entry `(f, n / f)`, where `f`
is the residue degree of the fixed field of any point stabilizer. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      {(letI := ρ.mulAction
        ((fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree,
          n / (fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree))} := by
  let := ρ.mulAction
  have : IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  have : Nonempty (Fin n) := ⟨i⟩
  let := ((pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map, Finset.univ_unique, Finset.singleton_val, Multiset.map_singleton,
    ρ.splittingSymbol_entry_out (Subsingleton.elim _ _),
    ρ.finrank_fixedField_stabilizer_of_isTransitive hρ]

/-- A Galois set of size `f e` has splitting symbol `{(f, e)}` exactly when it is transitive and
the fixed field of a point stabilizer has residue degree `f`. The label `i` makes the size
positive. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (ρ : GaloisSet K (f * e)) (i : Fin (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔ ρ.IsTransitive ∧
      (letI := ρ.mulAction
      (fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = f) := by
  let := ρ.mulAction
  have hf : 0 < f := Nat.pos_of_mul_pos_right i.pos
  constructor
  · intro h
    have hρ : ρ.IsTransitive := by
      have hcard := congrArg Multiset.card h
      rw [card_splittingSymbol, Multiset.card_singleton, Nat.card_eq_one_iff_unique] at hcard
      exact ρ.isTransitive_def.2 ((pretransitive_iff_subsingleton_quotient _ _).2 hcard.1)
    rw [ρ.splittingSymbol_of_isTransitive hρ i, Multiset.singleton_inj, Prod.mk.injEq] at h
    exact ⟨hρ, h.1⟩
  · rintro ⟨hρ, hi⟩
    rw [ρ.splittingSymbol_of_isTransitive hρ i, hi, Nat.mul_div_cancel_left _ hf]

/-- The trivial Galois set of size `n` is the split algebra `K ^ n`: its splitting symbol is `n`
copies of `(1, 1)`. -/
@[simp]
theorem splittingSymbol_trivial : (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  have hmem : ∀ x ∈ (trivial K n).splittingSymbol, x = (1, 1) := by
    intro x hx
    obtain ⟨i, rfl⟩ := (trivial K n).mem_splittingSymbol.1 hx
    simp
  rw [Multiset.eq_replicate]
  refine ⟨?_, hmem⟩
  have h := (trivial K n).sum_map_mul_splittingSymbol
  rwa [Multiset.map_congr rfl (g := fun _ ↦ 1) fun x hx ↦ by simp [hmem x hx], Multiset.map_const',
    Multiset.sum_replicate, smul_eq_mul, mul_one] at h

/-- **Galois sets with splitting symbol `{(f, e)}` and subextensions.** Summed over the labelled
Galois sets of size `f e` with splitting symbol `{(f, e)}`, any weight `g` of the fixed field of the
stabilizer of a label `i` is `(f e - 1)!` times the sum of `g` over the subextensions of
`SeparableClosure K` of degree `f e` and residue degree `f`. -/
theorem tsum_splittingSymbol_eq_singleton {f e : ℕ} (i : Fin (f * e))
    (g : IntermediateField K (SeparableClosure K) → ℝ≥0∞) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        (letI := ρ.1.mulAction
        g (fixedField (stabilizer Gal(SeparableClosure K/K) i))) =
      ((f * e - 1).factorial : ℝ≥0∞) *
        ∑' L : {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f}, g L.1 := by
  -- Restrict `g` to residue degree `f` and apply the transitive bridge.
  let g' : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦
    if L.inertiaDegree = f then g L else 0
  have hρ : ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
      (letI := ρ.1.mulAction
      g (fixedField (stabilizer Gal(SeparableClosure K/K) i))) =
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        (letI := ρ.1.mulAction
        g' (fixedField (stabilizer Gal(SeparableClosure K/K) i))) := by
    refine (tsum_subtype {ρ : GaloisSet K (f * e) | ρ.splittingSymbol = {(f, e)}}
      fun ρ ↦ letI := ρ.mulAction; g (fixedField (stabilizer Gal(SeparableClosure K/K) i))).trans <|
      (tsum_congr fun ρ ↦ ?_).trans (tsum_subtype {ρ : GaloisSet K (f * e) | ρ.IsTransitive}
        fun ρ ↦ letI := ρ.mulAction; g' (fixedField (stabilizer Gal(SeparableClosure K/K) i))).symm
    by_cases h : ρ.IsTransitive <;>
      simp [Set.indicator, g', ρ.splittingSymbol_eq_singleton_iff i, h]
  have hL : ∑' L : {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = f * e}, g' L.1 =
      ∑' L : {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e ∧ L.inertiaDegree = f}, g L.1 := by
    refine (tsum_subtype {L : IntermediateField K (SeparableClosure K) |
      Module.finrank K L = f * e} g').trans <| (tsum_congr fun L ↦ ?_).trans
      (tsum_subtype {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = f * e ∧ L.inertiaDegree = f} g).symm
    by_cases h₁ : Module.finrank K L = f * e <;> by_cases h₂ : L.inertiaDegree = f <;>
      simp [Set.indicator, g', h₁, h₂]
  rw [hρ, tsum_isTransitive i g', hL]

end GaloisSet

/-- **The transitive mass by residue degree** [Bhargava 2007, §2]: for `f, e ≥ 1`, the labelled
Galois sets of size `f e` with splitting symbol `{(f, e)}` have mass
`(1 / (f e)!) ∑_ρ q ^ (-d(ρ)) = 1 / (f q ^ (f (e - 1)))`, where `q` is the residue cardinality of
`K`. These are the Galois sets of the field extensions of `K` of degree `f e` and residue
degree `f`. The sum is in `ℝ≥0∞`, so the equation also asserts that it is finite. -/
theorem etaleMass_isTransitive_splittingSymbol {f e : ℕ} (hf : f ≠ 0) (he : e ≠ 0) :
    ((f * e).factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  have hn : 0 < f * e := Nat.mul_pos (Nat.pos_of_ne_zero hf) (Nat.pos_of_ne_zero he)
  let i : Fin (f * e) := ⟨0, hn⟩
  -- These Galois sets are transitive, so `d(ρ)` is the discriminant exponent at the label `i`.
  have h := GaloisSet.tsum_splittingSymbol_eq_singleton (K := K) i
    fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent
  beta_reduce at h
  rw [tsum_congr fun ρ ↦ by
      rw [ρ.1.discriminantExponent_of_isTransitive
        ((ρ.1.splittingSymbol_eq_singleton_iff i).1 ρ.2).1 i],
    h, tsum_inertiaDegree_eq hf]
  -- It remains to compute `(f e)!⁻¹ · (f e - 1)! · e / Q = 1 / (f Q)` with `Q = q ^ (f (e - 1))`.
  have hfac : ((f * e).factorial : ℝ≥0∞) = f * e * ((f * e - 1).factorial : ℝ≥0∞) := by
    rw [← Nat.mul_factorial_pred hn.ne']
    push_cast
    ring
  have ha : ((f * e - 1).factorial : ℝ≥0∞) ≠ 0 := by simp [Nat.factorial_ne_zero]
  have he' : (e : ℝ≥0∞) ≠ 0 := by simp [he]
  rw [hfac, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one,
    ENNReal.mul_inv (by simp) (.inr ha), ENNReal.mul_inv (by simp) (by simp),
    ENNReal.mul_inv (by simp) (by simp)]
  calc _ = (f : ℝ≥0∞)⁻¹ * ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))⁻¹ *
          (((e : ℝ≥0∞)⁻¹ * e) *
            (((f * e - 1).factorial : ℝ≥0∞)⁻¹ * ((f * e - 1).factorial : ℝ≥0∞))) := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel he' (by simp), ENNReal.inv_mul_cancel ha (by simp), mul_one,
        mul_one]

end TauCeti
