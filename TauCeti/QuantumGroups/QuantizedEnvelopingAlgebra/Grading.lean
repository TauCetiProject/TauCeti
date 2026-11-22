/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic
public import TauCeti.RingTheory.GradedAlgebra.Generators

import Mathlib.Algebra.Ring.Action.ConjAct
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Algebra.DirectSum.Supported

/-!
# Root-lattice grading on a quantized enveloping algebra

Assigning `Eᵢ` degree `εᵢ := Finsupp.single i 1` (`εᵢ ∈ ι →₀ ℤ`), `Fᵢ` degree `-εᵢ`, and `K_y`
degree `0` equips `QuantizedEnvelopingAlgebra D q` with homogeneous pieces `gradedPiece D q c`
(`c : ι →₀ ℤ`) for arbitrary `q : K`, without finiteness assumptions on `ι`, decidable equality
on `ι`, or freeness assumptions on `X` and `Y`. Neither `gradedPiece`, its `SetLike.GradedMonoid`
instance, the divided-power and map-preservation lemmas, nor the toral conjugation formula
(`k_mul_mul_k_neg_of_mem_gradedPiece`) requires `[DecidableEq ι]`.

Under `[DecidableEq ι]`, the homogeneous pieces form an internal direct sum
(`isInternal_gradedPiece`), yielding the `(ι →₀ ℤ)`-grading `instGradedAlgebra`, componentwise
membership (`mem_gradedPiece_iff`), and compatibility of `DirectSum.decompose` with `map`,
`rescale`, and `chevalleyInvolution`.

## Attribution

The word-span and direct-sum lift construction is adapted from
`TauCeti.Algebra.Lie.UniversalEnveloping.Grading` (via the shared `TauCeti.GradedAlgebra.wordSpan`
machinery in `TauCeti.RingTheory.GradedAlgebra.Generators`), itself adapted from
`Mei/Algebra/Lie/UniversalEnveloping/Grading.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).

## References

* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, American Mathematical Society, 1996, §4.7.
-/

public section

open DirectSum

namespace TauCeti.QuantizedEnvelopingAlgebra

section Degree

variable {ι Y : Type*}

/-- The formal root-lattice degree in `ι →₀ ℤ` of a generator: `+εᵢ` on `Eᵢ`, `-εᵢ` on `Fᵢ`, and
`0` on every toral generator `K_y`, where `εᵢ := Finsupp.single i 1`. -/
noncomputable def generatorDegree : Generator ι Y → (ι →₀ ℤ)
  | .e i => Finsupp.single i 1
  | .f i => -Finsupp.single i 1
  | .k _ => 0
@[simp] theorem generatorDegree_e (i : ι) :
    generatorDegree (.e i : Generator ι Y) = Finsupp.single i 1 := (rfl)
@[simp] theorem generatorDegree_f (i : ι) :
    generatorDegree (.f i : Generator ι Y) = -Finsupp.single i 1 := (rfl)
@[simp] theorem generatorDegree_k (y : Y) : generatorDegree (.k y : Generator ι Y) = 0 := (rfl)

end Degree

section Pieces

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- The homogeneous piece of `QuantizedEnvelopingAlgebra D q` of degree `c : ι →₀ ℤ`, spanned over
`K` by products of presentation generators whose degrees sum to `c`. -/
noncomputable def gradedPiece (D : CartanDatum ι X Y) (q : K) (c : ι →₀ ℤ) :
    Submodule K (QuantizedEnvelopingAlgebra D q) :=
  TauCeti.GradedAlgebra.wordSpan K (generator D q) generatorDegree c
theorem gradedPiece_def (D : CartanDatum ι X Y) (q : K) (c : ι →₀ ℤ) :
    gradedPiece D q c = Submodule.span K
      {x | ∃ l : List (Generator ι Y),
        (l.map generatorDegree).sum = c ∧ (l.map (generator D q)).prod = x} :=
  TauCeti.GradedAlgebra.wordSpan_def K (generator D q) generatorDegree c

variable {D : CartanDatum ι X Y} {q : K}

theorem word_mem_gradedPiece {c : ι →₀ ℤ} {l : List (Generator ι Y)}
    (hl : (l.map generatorDegree).sum = c) :
    (l.map (generator D q)).prod ∈ gradedPiece D q c :=
  TauCeti.GradedAlgebra.prod_mem_wordSpan_of_eq hl

/-- A submodule contains the degree-`c` piece `gradedPiece D q c` exactly when it contains every
generator word of total degree `c`. -/
theorem gradedPiece_le_iff (c : ι →₀ ℤ) (p : Submodule K (QuantizedEnvelopingAlgebra D q)) :
    gradedPiece D q c ≤ p ↔
      ∀ l : List (Generator ι Y), (l.map generatorDegree).sum = c →
        (l.map (generator D q)).prod ∈ p :=
  TauCeti.GradedAlgebra.wordSpan_le_iff c p

/-- Structural induction on `gradedPiece D q c` from generator words of degree `c` under zero,
addition, and `K`-scalar multiplication. -/
@[elab_as_elim]
theorem gradedPiece_induction {c : ι →₀ ℤ} {x : QuantizedEnvelopingAlgebra D q}
    {P : (x : QuantizedEnvelopingAlgebra D q) → x ∈ gradedPiece D q c → Prop}
    (hx : x ∈ gradedPiece D q c)
    (word : ∀ l : List (Generator ι Y), (hl : (l.map generatorDegree).sum = c) →
      P (l.map (generator D q)).prod (word_mem_gradedPiece hl))
    (zero : P 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (smul : ∀ (a : K) x hx, P x hx → P (a • x) (Submodule.smul_mem _ a hx)) : P x hx :=
  TauCeti.GradedAlgebra.wordSpan_induction hx word zero add smul

theorem generator_mem_gradedPiece (g : Generator ι Y) :
    generator D q g ∈ gradedPiece D q (generatorDegree g) :=
  TauCeti.GradedAlgebra.mem_wordSpan_self (generator D q) generatorDegree g
theorem e_mem_gradedPiece (i : ι) : e D q i ∈ gradedPiece D q (Finsupp.single i 1) := by
  simpa using generator_mem_gradedPiece (D := D) (q := q) (.e i)
theorem f_mem_gradedPiece (i : ι) : f D q i ∈ gradedPiece D q (-Finsupp.single i 1) := by
  simpa using generator_mem_gradedPiece (D := D) (q := q) (.f i)
theorem k_mem_gradedPiece (y : Y) : k D q y ∈ gradedPiece D q 0 := by
  simpa using generator_mem_gradedPiece (D := D) (q := q) (.k y)
theorem simpleK_mem_gradedPiece (i : ι) : simpleK D q i ∈ gradedPiece D q 0 :=
  simpleK_def D q i ▸ k_mem_gradedPiece (D.simpleTorus i)
theorem simpleKInv_mem_gradedPiece (i : ι) : simpleKInv D q i ∈ gradedPiece D q 0 :=
  simpleKInv_def D q i ▸ k_mem_gradedPiece (-D.simpleTorus i)

/-- Multiplication respects `gradedPiece D q`, giving a graded monoid structure for all `q : K`. -/
instance instGradedMonoid (D : CartanDatum ι X Y) (q : K) :
    SetLike.GradedMonoid (gradedPiece D q) :=
  inferInstanceAs (SetLike.GradedMonoid
    (TauCeti.GradedAlgebra.wordSpan K (generator D q) generatorDegree))

/-- The normalized raising generator `eᵢ = Kᵢ⁻¹ Eᵢ` lies in degree `εᵢ := Finsupp.single i 1`. -/
theorem normalizedE_mem_gradedPiece (i : ι) :
    normalizedE D q i ∈ gradedPiece D q (Finsupp.single i 1) := by
  rw [normalizedE_def, ← zero_add (Finsupp.single i 1)]
  exact SetLike.mul_mem_graded (simpleKInv_mem_gradedPiece i) (e_mem_gradedPiece i)

/-- The normalized lowering generator `fᵢ = Fᵢ Kᵢ` lies in degree `-εᵢ`
(`εᵢ := Finsupp.single i 1`). -/
theorem normalizedF_mem_gradedPiece (i : ι) :
    normalizedF D q i ∈ gradedPiece D q (-Finsupp.single i 1) := by
  rw [normalizedF_def, ← add_zero (-Finsupp.single i 1)]
  exact SetLike.mul_mem_graded (f_mem_gradedPiece i) (simpleK_mem_gradedPiece i)

/-- The `n`-th divided power of the raising generator `Eᵢ` lies in degree `n • εᵢ`
(`εᵢ := Finsupp.single i 1`) for any `q : K`, even when `[n]_(qᵢ)! = 0`. -/
theorem quantumDividedPower_e_mem_gradedPiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n ∈
      gradedPiece D q (n • Finsupp.single i 1) :=
  quantumDividedPower_mem_graded _ (e_mem_gradedPiece i) n

/-- The `n`-th divided power of the lowering generator `Fᵢ` lies in degree `-(n • εᵢ)`
(`εᵢ := Finsupp.single i 1`) for any `q : K`, even when `[n]_(qᵢ)! = 0`. -/
theorem quantumDividedPower_f_mem_gradedPiece (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n ∈
      gradedPiece D q (-(n • Finsupp.single i 1)) := by
  rw [← smul_neg]; exact quantumDividedPower_mem_graded _ (f_mem_gradedPiece i) n

/-- A Cartan-datum morphism `φ : CartanDatum.Hom D D'` carries `gradedPiece D q c` into
`gradedPiece D' q c`. -/
theorem map_mem_gradedPiece {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    map φ q x ∈ gradedPiece D' q c := by
  refine TauCeti.GradedAlgebra.map_mem_wordSpan (map φ q) (AddMonoidHom.id (ι →₀ ℤ)) ?_ hx
  rintro (_ | _ | _)
  · simpa using e_mem_gradedPiece (D := D') (q := q) _
  · simpa using f_mem_gradedPiece (D := D') (q := q) _
  · simpa using k_mem_gradedPiece (D := D') (q := q) _

/-- Diagonal rescaling `rescale D q s` preserves each homogeneous piece `gradedPiece D q c`. -/
theorem rescale_mem_gradedPiece (s : ι → Kˣ) {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    rescale D q s x ∈ gradedPiece D q c := by
  refine TauCeti.GradedAlgebra.map_mem_wordSpan (rescale D q s) (AddMonoidHom.id (ι →₀ ℤ)) ?_ hx
  rintro (_ | _ | _)
  · rw [generator_e, rescale_e]; exact Submodule.smul_mem _ _ (e_mem_gradedPiece _)
  · rw [generator_f, rescale_f]; exact Submodule.smul_mem _ _ (f_mem_gradedPiece _)
  · rw [generator_k, rescale_k]; exact k_mem_gradedPiece _

/-- `rescale D q s x` lies in `gradedPiece D q c` iff `x` lies in `gradedPiece D q c`. -/
@[simp]
theorem rescale_mem_gradedPiece_iff (s : ι → Kˣ) {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} :
    rescale D q s x ∈ gradedPiece D q c ↔ x ∈ gradedPiece D q c :=
  ⟨fun h => by simpa [← rescale_symm] using rescale_mem_gradedPiece (fun i => (s i)⁻¹) h,
    rescale_mem_gradedPiece s⟩

/-- The Chevalley involution sends `gradedPiece D q c` into `gradedPiece D q (-c)`. -/
theorem chevalleyInvolution_mem_gradedPiece {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    chevalleyInvolution D q x ∈ gradedPiece D q (-c) := by
  refine TauCeti.GradedAlgebra.map_mem_wordSpan (chevalleyInvolution D q)
    (-AddMonoidHom.id (ι →₀ ℤ)) ?_ hx
  rintro (_ | _ | _)
  · simpa using f_mem_gradedPiece _
  · simpa using e_mem_gradedPiece _
  · simpa using k_mem_gradedPiece _

/-- `chevalleyInvolution D q x` lies in `gradedPiece D q c` iff `x` lies in
`gradedPiece D q (-c)`. -/
@[simp]
theorem chevalleyInvolution_mem_gradedPiece_iff {c : ι →₀ ℤ}
    {x : QuantizedEnvelopingAlgebra D q} :
    chevalleyInvolution D q x ∈ gradedPiece D q c ↔ x ∈ gradedPiece D q (-c) :=
  ⟨fun h => by simpa using chevalleyInvolution_mem_gradedPiece h,
    fun h => neg_neg c ▸ chevalleyInvolution_mem_gradedPiece h⟩

private theorem k_mul_generator_mul_k_neg (y : Y) (g : Generator ι Y) :
    k D q y * generator D q g * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root (generatorDegree g)) y •
        generator D q g := by
  cases g with
  | e i => simp [k_mul_e_mul_k_neg]
  | f i => simp [k_mul_f_mul_k_neg]
  | k z => simp [add_right_comm y z (-y)]

private theorem kUnitsHom_conjAct_apply (y : Y) (z : QuantizedEnvelopingAlgebra D q) :
    MulSemiringAction.toAlgEquiv K (QuantizedEnvelopingAlgebra D q)
        (ConjAct.toConjAct (kUnitsHom D q (.ofAdd y))) z =
      k D q y * z * k D q (-y) := by
  simp only [MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct, val_kUnitsHom, val_inv_kUnitsHom]

private theorem k_mul_word_mul_k_neg (y : Y) (l : List (Generator ι Y)) :
    k D q y * (l.map (generator D q)).prod * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root (l.map generatorDegree).sum) y •
        (l.map (generator D q)).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rcases eq_or_ne q 0 with rfl | hq
    · cases g with
      | e _ | f _ => simp
      | k z =>
        simp only [List.map_cons, List.prod_cons, generator_k, generatorDegree_k, List.sum_cons,
          zero_add]
        rw [← mul_assoc (k D (0 : K) y), k_mul_k, add_comm y z, ← k_mul_k,
          mul_assoc (k D (0 : K) z), mul_assoc (k D (0 : K) z), ih, mul_smul_comm]
    · simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, LinearMap.add_apply]
      rw [← kUnitsHom_conjAct_apply, map_mul, kUnitsHom_conjAct_apply, kUnitsHom_conjAct_apply,
        k_mul_generator_mul_k_neg, ih, smul_mul_smul_comm, ← zpow_add₀ hq]

/-- Conjugating `x ∈ gradedPiece D q c` by `K_y` multiplies it by `q^⟨∑ cᵢ αᵢ, y⟩`. -/
theorem k_mul_mul_k_neg_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    k D q y * x * k D q (-y) =
      q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • x := by
  rw [← kUnitsHom_conjAct_apply]
  induction hx using gradedPiece_induction with
  | word l hl => simpa only [kUnitsHom_conjAct_apply, hl] using k_mul_word_mul_k_neg y l
  | zero => rw [map_zero, smul_zero]
  | add _ _ _ _ ha hb => rw [map_add, ha, hb, smul_add]
  | smul _ _ _ ha => rw [map_smul, ha, smul_comm]

/-- Moving `K_y` from left to right past `x ∈ gradedPiece D q c` multiplies by `q^⟨∑ cᵢ αᵢ, y⟩`
(the weight pairing). -/
theorem k_mul_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    k D q y * x = q ^ D.pairing (Finsupp.linearCombination ℤ D.root c) y • (x * k D q y) := by
  rw [← mul_one (k D q y * x), ← k_neg_mul_k D q y, ← mul_assoc,
    k_mul_mul_k_neg_of_mem_gradedPiece y hx, smul_mul_assoc]

/-- Moving `K_y` from right to left past `x ∈ gradedPiece D q c` multiplies by
`q^(-⟨∑ cᵢ αᵢ, y⟩)` (the negated weight pairing). -/
theorem mul_k_of_mem_gradedPiece {c : ι →₀ ℤ} (y : Y)
    {x : QuantizedEnvelopingAlgebra D q} (hx : x ∈ gradedPiece D q c) :
    x * k D q y =
      q ^ (-D.pairing (Finsupp.linearCombination ℤ D.root c) y) • (k D q y * x) := by
  have h := k_mul_mul_k_neg_of_mem_gradedPiece (-y) hx
  rw [neg_neg, map_neg] at h
  rw [← one_mul (x * k D q y), ← k_mul_k_neg D q y, mul_assoc (k D q y),
    ← mul_assoc (k D q (-y)), h, mul_smul_comm]

end Pieces

section GradedAlgebra

variable {ι X Y K : Type*} [DecidableEq ι] [AddCommGroup X] [AddCommGroup Y] [Field K]
  {D : CartanDatum ι X Y} {q : K}

private noncomputable def decomposeAlgHom (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] ⨁ c, gradedPiece D q c :=
  lift
    { e i := of (fun c => gradedPiece D q c) (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩
      f i := of (fun c => gradedPiece D q c) (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩
      k y := of (fun c => gradedPiece D q c) 0 ⟨k D q y, k_mem_gradedPiece y⟩
      k_zero := by
        rw [one_def]
        refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl ?_)
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        exact k_zero D q
      k_mul_k y z := by
        rw [of_mul_of]
        refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (zero_add 0) ?_)
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        simpa only [SetLike.coe_gMul] using k_mul_k D q y z
      conjugate_e y i := by
        rw [of_mul_of, of_mul_of, ← of_smul]
        refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ ?_) <;>
          dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        · simp
        · simpa only [SetLike.coe_gMul, SetLike.val_smul] using k_mul_e_mul_k_neg D q y i
      conjugate_f y i := by
        rw [of_mul_of, of_mul_of, ← of_smul]
        refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ ?_) <;>
          dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        · simp
        · simpa only [SetLike.coe_gMul, SetLike.val_smul] using k_mul_f_mul_k_neg D q y i
      commutator_self i := by
        rw [of_mul_of, of_mul_of]
        have h₁ : of (fun c => gradedPiece D q c) (Finsupp.single i 1 + -Finsupp.single i 1)
            (GradedMonoid.GMul.mul (A := fun c => gradedPiece D q c)
              (⟨e D q i, e_mem_gradedPiece i⟩ : gradedPiece D q (Finsupp.single i 1))
              (⟨f D q i, f_mem_gradedPiece i⟩ : gradedPiece D q (-Finsupp.single i 1))) =
            of (fun c => gradedPiece D q c) 0
              ⟨e D q i * f D q i,
                (add_neg_cancel (Finsupp.single i (1 : ℤ))) ▸
                  SetLike.mul_mem_graded (e_mem_gradedPiece i) (f_mem_gradedPiece i)⟩ := by
          refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_neg_cancel _) ?_)
          dsimp only [GradedMonoid.mk, Subtype.coe_mk]
          simp only [SetLike.coe_gMul]
        have h₂ : of (fun c => gradedPiece D q c) (-Finsupp.single i 1 + Finsupp.single i 1)
            (GradedMonoid.GMul.mul (A := fun c => gradedPiece D q c)
              (⟨f D q i, f_mem_gradedPiece i⟩ : gradedPiece D q (-Finsupp.single i 1))
              (⟨e D q i, e_mem_gradedPiece i⟩ : gradedPiece D q (Finsupp.single i 1))) =
            of (fun c => gradedPiece D q c) 0
              ⟨f D q i * e D q i,
                (neg_add_cancel (Finsupp.single i (1 : ℤ))) ▸
                  SetLike.mul_mem_graded (f_mem_gradedPiece i) (e_mem_gradedPiece i)⟩ := by
          refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (neg_add_cancel _) ?_)
          dsimp only [GradedMonoid.mk, Subtype.coe_mk]
          simp only [SetLike.coe_gMul]
        rw [h₁, h₂, ← map_sub (of (fun c => gradedPiece D q c) 0),
          ← map_sub (of (fun c => gradedPiece D q c) 0), ← of_smul]
        refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl ?_)
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        simpa only [Submodule.coe_sub, SetLike.val_smul, simpleK_def, simpleKInv_def] using
          e_mul_f_sub_f_mul_e_self D q i
      commutator_ne {i j} hij := by
        rw [of_mul_of, of_mul_of, sub_eq_zero]
        refine of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) ?_)
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
        simpa only [SetLike.coe_gMul] using (commute_e_f D q hij).eq
      serre_e {i j} hij := by
        rw [serreSum_of, show (⟨serreSum D q (fun l => e D q l) i j, _⟩ :
          gradedPiece D q (D.serreLength i j • Finsupp.single i 1 + Finsupp.single j 1)) = 0 from
          Subtype.ext (serreE_eq_zero D q hij), map_zero]
      serre_f {i j} hij := by
        rw [serreSum_of, show (⟨serreSum D q (fun l => f D q l) i j, _⟩ :
          gradedPiece D q (D.serreLength i j • -Finsupp.single i 1 + -Finsupp.single j 1)) = 0 from
          Subtype.ext (serreF_eq_zero D q hij), map_zero] }

/-- `gradedPiece D q` forms an internal direct sum for every `q : K` (given `[DecidableEq ι]`),
giving unique finite homogeneous decompositions and a genuine `(ι →₀ ℤ)`-grading. -/
theorem isInternal_gradedPiece (D : CartanDatum ι X Y) (q : K) : IsInternal (gradedPiece D q) := by
  have hcoe : (DirectSum.coeAlgHom (gradedPiece D q)).comp (decomposeAlgHom D q) =
      AlgHom.id K _ := by ext <;> simp [decomposeAlgHom]
  have hf (g : Generator ι Y) :
      decomposeAlgHom D q (generator D q g) ∈
        DirectSum.summand K (fun c => ↥(gradedPiece D q c)) (generatorDegree g) := by
    cases g
    · simp only [generator_e, generatorDegree_e, decomposeAlgHom, lift_e]
      exact DirectSum.of_mem_summand (R := K) _ _
    · simp only [generator_f, generatorDegree_f, decomposeAlgHom, lift_f]
      exact DirectSum.of_mem_summand (R := K) _ _
    · simp only [generator_k, generatorDegree_k, decomposeAlgHom, lift_k]
      exact DirectSum.of_mem_summand (R := K) _ _
  let := GradedAlgebra.ofAlgHom (gradedPiece D q) (decomposeAlgHom D q) hcoe fun _ x =>
    TauCeti.GradedAlgebra.algHom_apply_of_mem_wordSpan (decomposeAlgHom D q)
      (AlgHom.congr_fun hcoe) hf x.property
  exact Decomposition.isInternal (gradedPiece D q)

/-- `QuantizedEnvelopingAlgebra D q` is internally `(ι →₀ ℤ)`-graded by `gradedPiece D q`. -/
noncomputable instance instGradedAlgebra (D : CartanDatum ι X Y) (q : K) :
    GradedAlgebra (gradedPiece D q) :=
  (isInternal_gradedPiece D q).gradedAlgebra

/-- An element `x` lies in `gradedPiece D q c` iff all homogeneous components of
`DirectSum.decompose (gradedPiece D q) x` of degree `d ≠ c` vanish. -/
theorem mem_gradedPiece_iff {c : ι →₀ ℤ} {x : QuantizedEnvelopingAlgebra D q} :
    x ∈ gradedPiece D q c ↔
      ∀ d, d ≠ c → (decompose (gradedPiece D q) x d : QuantizedEnvelopingAlgebra D q) = 0 := by
  have hsup : gradedPiece D q c = ⨆ d : ({c} : Set (ι →₀ ℤ)), gradedPiece D q d := by simp
  rw [hsup, TauCeti.DirectSum.mem_iSup_iff_decompose_eq_zero (gradedPiece D q) {c}]
  simp [Set.mem_singleton_iff]

@[simp] theorem decompose_e (i : ι) :
    decompose (gradedPiece D q) (e D q i) =
      of (fun c => gradedPiece D q c) (Finsupp.single i 1) ⟨e D q i, e_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (e_mem_gradedPiece i)
@[simp] theorem decompose_f (i : ι) :
    decompose (gradedPiece D q) (f D q i) =
      of (fun c => gradedPiece D q c) (-Finsupp.single i 1) ⟨f D q i, f_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (f_mem_gradedPiece i)
@[simp] theorem decompose_k (y : Y) :
    decompose (gradedPiece D q) (k D q y) =
      of (fun c => gradedPiece D q c) 0 ⟨k D q y, k_mem_gradedPiece y⟩ :=
  decompose_of_mem (gradedPiece D q) (k_mem_gradedPiece y)
@[simp] theorem decompose_simpleK (i : ι) :
    decompose (gradedPiece D q) (simpleK D q i) =
      of (fun c => gradedPiece D q c) 0 ⟨simpleK D q i, simpleK_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (simpleK_mem_gradedPiece i)
@[simp] theorem decompose_simpleKInv (i : ι) :
    decompose (gradedPiece D q) (simpleKInv D q i) =
      of (fun c => gradedPiece D q c) 0 ⟨simpleKInv D q i, simpleKInv_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (simpleKInv_mem_gradedPiece i)

/-- `decompose (gradedPiece D q)` sends `normalizedE D q i` to degree `Finsupp.single i 1`. -/
@[simp] theorem decompose_normalizedE (i : ι) :
    decompose (gradedPiece D q) (normalizedE D q i) =
      of (fun c => gradedPiece D q c) (Finsupp.single i 1)
        ⟨normalizedE D q i, normalizedE_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (normalizedE_mem_gradedPiece i)

/-- `decompose (gradedPiece D q)` sends `normalizedF D q i` to degree `-Finsupp.single i 1`. -/
@[simp] theorem decompose_normalizedF (i : ι) :
    decompose (gradedPiece D q) (normalizedF D q i) =
      of (fun c => gradedPiece D q c) (-Finsupp.single i 1)
        ⟨normalizedF D q i, normalizedF_mem_gradedPiece i⟩ :=
  decompose_of_mem (gradedPiece D q) (normalizedF_mem_gradedPiece i)

/-- A Cartan-datum morphism `φ : CartanDatum.Hom D D'` induces a graded `K`-algebra homomorphism
`gradedPiece D q →ₐᵍ[K] gradedPiece D' q`. -/
noncomputable def mapGradedAlgHom {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (q : K) :
    gradedPiece D q →ₐᵍ[K] gradedPiece D' q where
  __ := map φ q
  map_mem hx := map_mem_gradedPiece φ hx

/-- The underlying `K`-algebra homomorphism of `mapGradedAlgHom φ q` is `map φ q`. -/
@[simp]
theorem mapGradedAlgHom_toAlgHom {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (q : K) :
    (mapGradedAlgHom φ q).toAlgHom = map φ q :=
  (rfl)

/-- Evaluating `mapGradedAlgHom φ q` agrees with `map φ q`. -/
@[simp]
theorem mapGradedAlgHom_apply {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (q : K)
    (x : QuantizedEnvelopingAlgebra D q) :
    mapGradedAlgHom φ q x = map φ q x :=
  (rfl)

/-- The graded algebra homomorphism induced by the identity Cartan-datum morphism is the
identity. -/
@[simp]
theorem mapGradedAlgHom_id (D : CartanDatum ι X Y) (q : K) :
    mapGradedAlgHom (CartanDatum.Hom.id D) q = GradedAlgHom.id K (gradedPiece D q) :=
  GradedAlgHom.coe_toAlgHom_injective (map_id D q)

/-- Functoriality of `mapGradedAlgHom` under composition of Cartan-datum morphisms. -/
theorem mapGradedAlgHom_comp {X' Y' X'' Y'' : Type*}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup X''] [AddCommGroup Y'']
    {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}
    (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') (q : K) :
    mapGradedAlgHom (ψ.comp φ) q = (mapGradedAlgHom ψ q).comp (mapGradedAlgHom φ q) :=
  GradedAlgHom.coe_toAlgHom_injective (map_comp ψ φ q)

/-- `map φ q` commutes with homogeneous projections onto `gradedPiece`. -/
@[simp]
theorem coe_decompose_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (q : K)
    (x : QuantizedEnvelopingAlgebra D q) (c : ι →₀ ℤ) :
    (decompose (gradedPiece D' q) (map φ q x) c : QuantizedEnvelopingAlgebra D' q) =
      map φ q (decompose (gradedPiece D q) x c : QuantizedEnvelopingAlgebra D q) :=
  (GradedRingHom.map_directSumDecompose (gradedPiece D q) (gradedPiece D' q)
    (mapGradedAlgHom φ q).toGradedRingHom).symm

/-- Diagonal rescaling `rescale D q s` as a graded `K`-algebra endomorphism on `gradedPiece D q`. -/
noncomputable def rescaleGradedAlgHom (D : CartanDatum ι X Y) (q : K) (s : ι → Kˣ) :
    gradedPiece D q →ₐᵍ[K] gradedPiece D q where
  __ := (rescale D q s).toAlgHom
  map_mem hx := rescale_mem_gradedPiece s hx

/-- The underlying `K`-algebra homomorphism of `rescaleGradedAlgHom D q s` is
`(rescale D q s).toAlgHom`. -/
@[simp]
theorem rescaleGradedAlgHom_toAlgHom (D : CartanDatum ι X Y) (q : K) (s : ι → Kˣ) :
    (rescaleGradedAlgHom D q s).toAlgHom = (rescale D q s).toAlgHom :=
  (rfl)

/-- Evaluating `rescaleGradedAlgHom D q s` agrees with `rescale D q s`. -/
@[simp]
theorem rescaleGradedAlgHom_apply (D : CartanDatum ι X Y) (q : K) (s : ι → Kˣ)
    (x : QuantizedEnvelopingAlgebra D q) :
    rescaleGradedAlgHom D q s x = rescale D q s x :=
  (rfl)

/-- Rescaling by the constant-`1` family is the identity graded algebra endomorphism. -/
@[simp]
theorem rescaleGradedAlgHom_one (D : CartanDatum ι X Y) (q : K) :
    rescaleGradedAlgHom D q 1 = GradedAlgHom.id K (gradedPiece D q) :=
  GradedAlgHom.coe_toAlgHom_injective (by ext <;> simp)

/-- Rescaling by the pointwise product `s * t` equals the composite of the two graded algebra
endomorphisms. -/
theorem rescaleGradedAlgHom_mul (D : CartanDatum ι X Y) (q : K) (s t : ι → Kˣ) :
    rescaleGradedAlgHom D q (s * t) =
      (rescaleGradedAlgHom D q s).comp (rescaleGradedAlgHom D q t) :=
  GradedAlgHom.coe_toAlgHom_injective (by ext <;> simp [smul_smul, mul_comm])

/-- `rescale D q s` commutes with homogeneous projections onto `gradedPiece D q`. -/
@[simp]
theorem coe_decompose_rescale (s : ι → Kˣ) (x : QuantizedEnvelopingAlgebra D q) (c : ι →₀ ℤ) :
    (decompose (gradedPiece D q) (rescale D q s x) c : QuantizedEnvelopingAlgebra D q) =
      rescale D q s (decompose (gradedPiece D q) x c : QuantizedEnvelopingAlgebra D q) :=
  (GradedRingHom.map_directSumDecompose (gradedPiece D q) (gradedPiece D q)
    (rescaleGradedAlgHom D q s).toGradedRingHom).symm

/-- The degree-`c` component of `chevalleyInvolution D q x` is the image of the degree-`(-c)`
component of `x`. -/
@[simp]
theorem coe_decompose_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) (c : ι →₀ ℤ) :
    (decompose (gradedPiece D q) (chevalleyInvolution D q x) c :
        QuantizedEnvelopingAlgebra D q) =
      chevalleyInvolution D q
        (decompose (gradedPiece D q) x (-c) : QuantizedEnvelopingAlgebra D q) := by
  have h := DirectSum.map_decompose_shift (gradedPiece D q) (gradedPiece D q)
    (chevalleyInvolution D q : QuantizedEnvelopingAlgebra D q →+ QuantizedEnvelopingAlgebra D q)
    (fun d : ι →₀ ℤ => -d) neg_injective
    (fun _ _ hx => chevalleyInvolution_mem_gradedPiece hx) (-c) x
  dsimp only at h
  rw [neg_neg] at h
  simpa only [AddMonoidHom.coe_ofClass] using h.symm

end GradedAlgebra
end TauCeti.QuantizedEnvelopingAlgebra
