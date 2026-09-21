/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading

/-!
# Graded derivations of a path algebra, freely determined by the arrows

Give every arrow `e` of a finite quiver `Q` an integer degree `wt e`. The path algebra `kQ` is then
`ℤ`-graded by `TauCeti.PathAlgebra.gradeBy k wt`, and a *degree `+1` graded derivation* of `kQ` is a
`k`-linear endomorphism `d` obeying the signed Leibniz rule

```text
d (x * y) = d x * y + (-1) ^ p • (x * d y)
```

for a left factor `x` homogeneous of degree `p`.

Such a derivation is free on the arrows. An assignment `f` sending an arrow `e : a ⟶ b` into the
corner `e_b (kQ) e_a` extends to the graded derivation `TauCeti.PathAlgebra.liftDerivation`, which
kills every vertex idempotent and takes the value `f e` on `e`, and it is the only one. Its value on
a path is read off from the recursion

```text
d (e ⬝ p) = f e ⬝ p + (-1) ^ (wt e) • (e ⬝ d p),
```

which the later-factor-first multiplication of Tau Ceti turns into an induction along `cons`.

The derivation is graded for *every* arrow weight at once: if a second weight `g`, valued in any
additive commutative monoid, gives `f e` the degree `g e + δ` for one fixed shift `δ`, then `d`
raises the `g`-degree by `δ`. Taking `g = wt` and `δ = 1` is the cohomological statement, and a
second weight with `δ = 0` is the Adams grading of a differential graded path algebra.

Finally, `d ∘ d` is again a derivation, an unsigned one, so it vanishes as soon as it vanishes on
the arrows; together with the two previous paragraphs this packages `d` as the differential of a
differential graded algebra.

## Main definitions

* `TauCeti.PathAlgebra.liftDerivation`: the graded derivation of `kQ` extending an assignment `f` of
  a corner element to each arrow.

## Main results

* `TauCeti.PathAlgebra.liftDerivation_ofArrow`: the derivation extends the assignment.
* `TauCeti.PathAlgebra.liftDerivation_mul`: **the graded Leibniz rule**.
* `TauCeti.PathAlgebra.liftDerivation_unique`: **a graded derivation is determined by its values on
  the arrows** and its vanishing on the vertex idempotents.
* `TauCeti.PathAlgebra.liftDerivation_mem_gradeBy`: the derivation shifts the grading by an
  arbitrary arrow weight by a fixed amount, provided the assignment does.
* `TauCeti.PathAlgebra.liftDerivation_sq_zero`: the square of the derivation vanishes as soon
  as it vanishes on the arrows.
* `TauCeti.PathAlgebra.isDGAlgebra_liftDerivation`: **the resulting differential graded algebra**.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.5, and T. Etgü and Y. Lekili, *Koszul
  duality patterns in Floer theory*, Section 4, where the differential of a Ginzburg differential
  graded algebra is prescribed on the arrows of a quiver and extended by the Leibniz rule.
-/

public section

namespace TauCeti

universe u v w

namespace PathAlgebra

/-- The value of `TauCeti.PathAlgebra.liftDerivation` on a basis path. The recursion is along the
last arrow of the path, which the later-factor-first multiplication writes first. -/
private noncomputable def liftDerivationPath (k : Type w) [CommRing k] {Q : Type u} [Quiver.{v} Q]
    (wt : ∀ {a b : Q}, (a ⟶ b) → ℤ) (f : ∀ {a b : Q}, (a ⟶ b) → pathAlgebra k Q) :
    ∀ {a b : Q}, _root_.Quiver.Path a b → pathAlgebra k Q
  | _, _, .nil => 0
  | _, _, .cons p e =>
      f e * ofPath ⟨_, _, p⟩ + (wt e).negOnePow • (ofArrow e * liftDerivationPath k wt f p)

section Path

variable (k : Type w) [CommRing k] {Q : Type u} [Quiver.{v} Q]
  (wt : ∀ {a b : Q}, (a ⟶ b) → ℤ) (f : ∀ {a b : Q}, (a ⟶ b) → pathAlgebra k Q)

private theorem liftDerivationPath_nil (a : Q) :
    liftDerivationPath k wt f (.nil : _root_.Quiver.Path a a) = 0 := by
  simp [liftDerivationPath]

private theorem liftDerivationPath_cons {a b c : Q} (p : _root_.Quiver.Path a b) (e : b ⟶ c) :
    liftDerivationPath k wt f (p.cons e) =
      f e * ofPath ⟨a, b, p⟩ + (wt e).negOnePow • (ofArrow e * liftDerivationPath k wt f p) := by
  simp [liftDerivationPath]

end Path

section Lift

variable (k : Type w) [CommRing k] {Q : Type u} [Quiver.{v} Q] [Finite Q]
  (wt : ∀ {a b : Q}, (a ⟶ b) → ℤ) (f : ∀ {a b : Q}, (a ⟶ b) → pathAlgebra k Q)

/-- **The graded derivation of a path algebra extending an assignment on arrows.** Arrows are given
the integer degrees `wt`, and `f e` is the value of the derivation on the arrow `e`; for the Leibniz
rule to hold, `f e` must lie in the corner of `kQ` cut out by the endpoints of `e`. -/
noncomputable def liftDerivation : pathAlgebra k Q →ₗ[k] pathAlgebra k Q :=
  liftLinear k fun x => liftDerivationPath k wt f x.2.2

private theorem liftDerivation_ofPath (x : Quiver.TotalPath Q) :
    liftDerivation k wt f (ofPath x) = liftDerivationPath k wt f x.2.2 :=
  liftLinear_ofPath k _ x

@[simp]
theorem liftDerivation_vertexIdempotent (v : Q) :
    liftDerivation k wt f (vertexIdempotent k v) = 0 := by
  rw [vertexIdempotent_eq_ofPath, liftDerivation_ofPath, liftDerivationPath_nil]

variable (hfl : ∀ {a b : Q} (e : a ⟶ b), vertexIdempotent k b * f e = f e)
  (hfr : ∀ {a b : Q} (e : a ⟶ b), f e * vertexIdempotent k a = f e)

include hfl in
/-- The derivation of a path lies in the left corner cut out by the target of the path. -/
private theorem vertexIdempotent_mul_liftDerivation_ofPath (x : Quiver.TotalPath Q) :
    vertexIdempotent k x.2.1 * liftDerivation k wt f (ofPath x) =
      liftDerivation k wt f (ofPath x) := by
  obtain ⟨a, b, p⟩ := x
  rw [liftDerivation_ofPath]
  induction p with
  | nil => rw [liftDerivationPath_nil, mul_zero]
  | cons p e ih =>
      rw [liftDerivationPath_cons, mul_add, ← mul_assoc, hfl e, mul_smul_comm, ← mul_assoc,
        ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]

include hfr in
/-- **The derivation extends the assignment on arrows.**  Deliberately not a `simp` lemma:
`TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes its left-hand side. -/
theorem liftDerivation_ofArrow {a b : Q} (e : a ⟶ b) :
    liftDerivation k wt f (ofArrow e) = f e := by
  have h : (ofPath ⟨a, b, (_root_.Quiver.Path.nil).cons e⟩ : pathAlgebra k Q) = ofArrow e := by
    rw [← ofArrow_mul_ofPath, ← vertexIdempotent_eq_ofPath, ofArrow_eq_ofPath,
      ofPath_mul_vertexIdempotent]
  rw [← h, liftDerivation_ofPath, liftDerivationPath_cons, liftDerivationPath_nil, mul_zero,
    smul_zero, add_zero, ← vertexIdempotent_eq_ofPath, hfr e]

include hfl in
/-- **A vertex idempotent passes through the derivation**: it is a cycle of degree `0`. -/
private theorem liftDerivation_vertexIdempotent_mul (v : Q) (z : pathAlgebra k Q) :
    liftDerivation k wt f (vertexIdempotent k v * z) =
      vertexIdempotent k v * liftDerivation k wt f z := by
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
  | single x r =>
      rw [single_eq_smul_ofPath, mul_smul_comm, map_smul, map_smul, mul_smul_comm]
      congr 1
      obtain ⟨a, b, p⟩ := x
      rcases eq_or_ne v b with rfl | hv
      · rw [vertexIdempotent_mul_ofPath,
          vertexIdempotent_mul_liftDerivation_ofPath k wt f hfl ⟨a, v, p⟩]
      · rw [vertexIdempotent_mul_ofPath_of_ne _ hv, map_zero,
          ← vertexIdempotent_mul_liftDerivation_ofPath k wt f hfl ⟨a, b, p⟩, ← mul_assoc,
          vertexIdempotent_mul_vertexIdempotent_of_ne hv, zero_mul]

include hfl hfr in
/-- **The Leibniz rule against an arrow.** -/
theorem liftDerivation_ofArrow_mul {b c : Q} (e : b ⟶ c) (z : pathAlgebra k Q) :
    liftDerivation k wt f (ofArrow e * z) =
      f e * z + (wt e).negOnePow • (ofArrow e * liftDerivation k wt f z) := by
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, mul_add, mul_add, smul_add]
      abel
  | single x r =>
      rw [single_eq_smul_ofPath, mul_smul_comm, map_smul, map_smul, mul_smul_comm, mul_smul_comm,
        smul_comm (wt e).negOnePow r, ← smul_add]
      congr 1
      obtain ⟨a, b', p⟩ := x
      rcases eq_or_ne b' b with rfl | hb
      · rw [ofArrow_mul_ofPath, liftDerivation_ofPath, liftDerivation_ofPath,
          liftDerivationPath_cons]
      · rw [ofArrow_eq_ofPath, ofPath_mul_ofPath_of_not_composable hb, map_zero,
          ← hfr e, mul_assoc, vertexIdempotent_mul_ofPath_of_ne _ (Ne.symm hb), mul_zero,
          ← vertexIdempotent_mul_liftDerivation_ofPath k wt f hfl ⟨a, b', p⟩, ← mul_assoc,
          ofPath_mul_vertexIdempotent_of_ne _ hb, zero_mul, zero_add, smul_zero]

include hfl hfr in
/-- **The Leibniz rule against a basis path**, with the sign given by the weight of the path. -/
private theorem liftDerivation_ofPath_mul (x : Quiver.TotalPath Q) (y : pathAlgebra k Q) :
    liftDerivation k wt f (ofPath x * y) =
      liftDerivation k wt f (ofPath x) * y +
        (x.2.2.addWeight wt).negOnePow • (ofPath x * liftDerivation k wt f y) := by
  obtain ⟨a, b, p⟩ := x
  induction p with
  | nil =>
      rw [← vertexIdempotent_eq_ofPath, liftDerivation_vertexIdempotent_mul k wt f hfl,
        liftDerivation_vertexIdempotent, zero_mul, zero_add,
        _root_.Quiver.Path.addWeight_nil, Int.negOnePow_zero, one_smul]
  | cons p e ih =>
      rw [← ofArrow_mul_ofPath, mul_assoc, liftDerivation_ofArrow_mul k wt f hfl hfr, ih,
        liftDerivation_ofArrow_mul k wt f hfl hfr, _root_.Quiver.Path.addWeight_cons,
        Int.negOnePow_add]
      simp only [mul_add, add_mul, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      rw [mul_comm (wt e).negOnePow, ← add_assoc]

include hfl hfr in
/-- **The graded Leibniz rule**: on a homogeneous left factor of degree `m`, the derivation obeys
the Koszul sign rule. -/
theorem liftDerivation_mul {m : ℤ} {x : pathAlgebra k Q} (hx : x ∈ gradeBy k wt m)
    (y : pathAlgebra k Q) :
    liftDerivation k wt f (x * y) =
      liftDerivation k wt f x * y + m.negOnePow • (x * liftDerivation k wt f y) := by
  rw [gradeBy_eq_span_range] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨⟨x, hx⟩, rfl⟩ := hu
      rw [liftDerivation_ofPath_mul k wt f hfl hfr, hx]
  | zero => simp
  | add u v _ _ ihu ihv =>
      rw [add_mul, map_add, ihu, ihv, map_add, add_mul, add_mul, smul_add]
      abel
  | smul r u _ ih =>
      rw [smul_mul_assoc, map_smul, ih, smul_add, smul_mul_assoc, map_smul, smul_mul_assoc,
        smul_comm m.negOnePow r]

/-! ### Gradings, uniqueness, and the differential graded algebra -/

variable {M : Type*} [AddCommMonoid M] (g : ∀ {a b : Q}, (a ⟶ b) → M) (δ : M)

private theorem liftDerivationPath_mem_gradeBy
    (hg : ∀ {a b : Q} (e : a ⟶ b), f e ∈ gradeBy k g (g e + δ)) {a b : Q}
    (p : _root_.Quiver.Path a b) :
    liftDerivationPath k wt f p ∈ gradeBy k g (p.addWeight g + δ) := by
  induction p with
  | nil => rw [liftDerivationPath_nil]; exact zero_mem _
  | cons p e ih =>
      rw [liftDerivationPath_cons, _root_.Quiver.Path.addWeight_cons]
      refine add_mem ?_ ((Submodule.smul_mem_iff' _ _).2 ?_)
      · have h : g e + δ + p.addWeight g = p.addWeight g + g e + δ := by abel
        exact h ▸ gradeBy_mul_gradeBy_le _ _
          (Submodule.mul_mem_mul (hg e) (ofPath_mem_gradeBy g ⟨_, _, p⟩))
      · have h : g e + (p.addWeight g + δ) = p.addWeight g + g e + δ := by abel
        exact h ▸ gradeBy_mul_gradeBy_le _ _
          (Submodule.mul_mem_mul (ofArrow_mem_gradeBy g e) ih)

/-- **The derivation shifts every arrow grading by a fixed amount**, provided the assignment does:
if `f e` is homogeneous of degree `g e + δ` for the arrow weight `g`, then the derivation raises the
`g`-degree by `δ`.  With `g = wt` and `δ = 1` this is the cohomological degree of a differential;
with a second weight and `δ = 0` it is the invariance of an Adams grading. -/
theorem liftDerivation_mem_gradeBy
    (hg : ∀ {a b : Q} (e : a ⟶ b), f e ∈ gradeBy k g (g e + δ))
    {m : M} {x : pathAlgebra k Q} (hx : x ∈ gradeBy k g m) :
    liftDerivation k wt f x ∈ gradeBy k g (m + δ) := by
  rw [gradeBy_eq_span_range] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨⟨x, hx⟩, rfl⟩ := hu
      rw [liftDerivation_ofPath]
      exact hx ▸ liftDerivationPath_mem_gradeBy k wt f g δ hg x.2.2
  | zero => simp
  | add u v _ _ ihu ihv => rw [map_add]; exact add_mem ihu ihv
  | smul r u _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

include hfl hfr in
/-- **A graded derivation is determined by its values on the arrows.** -/
theorem liftDerivation_unique (D : pathAlgebra k Q →ₗ[k] pathAlgebra k Q)
    (hvertex : ∀ v : Q, D (vertexIdempotent k v) = 0)
    (hleibniz : ∀ {m : ℤ} {x : pathAlgebra k Q}, x ∈ gradeBy k wt m → ∀ y : pathAlgebra k Q,
      D (x * y) = D x * y + m.negOnePow • (x * D y))
    (harrow : ∀ {a b : Q} (e : a ⟶ b), D (ofArrow e) = f e) :
    D = liftDerivation k wt f := by
  refine LinearMap.ext fun z => ?_
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single x r =>
      rw [single_eq_smul_ofPath, map_smul, map_smul]
      congr 1
      obtain ⟨a, b, p⟩ := x
      induction p with
      | nil => rw [← vertexIdempotent_eq_ofPath, hvertex, liftDerivation_vertexIdempotent]
      | cons p e ih =>
          rw [← ofArrow_mul_ofPath, hleibniz (ofArrow_mem_gradeBy wt e), harrow, ih,
            ← liftDerivation_ofArrow_mul k wt f hfl hfr]

variable (hf : ∀ {a b : Q} (e : a ⟶ b), f e ∈ gradeBy k wt (wt e + 1))
  (hsq : ∀ {a b : Q} (e : a ⟶ b), liftDerivation k wt f (f e) = 0)

include hfl hfr hf hsq in
/-- The square of the derivation is an ordinary, unsigned derivation: the two signs of the graded
Leibniz rule cancel.  This is the induction step of
`TauCeti.PathAlgebra.liftDerivation_sq_zero`. -/
private theorem liftDerivation_sq_zero_ofArrow_mul {b c : Q} (e : b ⟶ c)
    (z : pathAlgebra k Q) :
    liftDerivation k wt f (liftDerivation k wt f (ofArrow e * z)) =
      ofArrow e * liftDerivation k wt f (liftDerivation k wt f z) := by
  rw [liftDerivation_ofArrow_mul k wt f hfl hfr, map_add, LinearMap.CompatibleSMul.map_smul,
    liftDerivation_mul k wt f hfl hfr (hf e), hsq, zero_mul, zero_add,
    liftDerivation_ofArrow_mul k wt f hfl hfr, Int.negOnePow_succ, Units.neg_smul, smul_add,
    smul_smul, Int.units_mul_self, one_smul, ← add_assoc, neg_add_cancel, zero_add]

include hfl hfr hf hsq in
/-- **The square of the derivation vanishes** as soon as it vanishes on the arrows. -/
theorem liftDerivation_sq_zero (z : pathAlgebra k Q) :
    liftDerivation k wt f (liftDerivation k wt f z) = 0 := by
  have hpath : ∀ x : Quiver.TotalPath Q,
      liftDerivation k wt f (liftDerivation k wt f (ofPath x)) = 0 := by
    rintro ⟨a, b, p⟩
    induction p with
    | nil => rw [← vertexIdempotent_eq_ofPath, liftDerivation_vertexIdempotent, map_zero]
    | cons p e ih =>
        rw [← ofArrow_mul_ofPath,
          liftDerivation_sq_zero_ofArrow_mul k wt f hfl hfr hf hsq, ih, mul_zero]
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | single x r => rw [single_eq_smul_ofPath, map_smul, map_smul, hpath, smul_zero]

include hfl hfr hf hsq in
/-- **The path algebra, graded by the arrow degrees `wt`, is a differential graded algebra** with
differential `TauCeti.PathAlgebra.liftDerivation`. -/
theorem isDGAlgebra_liftDerivation :
    IsDGAlgebra (gradeBy k wt) (liftDerivation k wt f) where
  map_mem hx := liftDerivation_mem_gradeBy k wt f wt 1 hf hx
  sq_zero := liftDerivation_sq_zero k wt f hfl hfr hf hsq
  leibniz hx y := liftDerivation_mul k wt f hfl hfr hx y

end Lift

end PathAlgebra

end TauCeti
