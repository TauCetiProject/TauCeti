/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The long exact homology sequence as an acyclic chain complex

Three `ℤ`-indexed families of objects `X₁ q`, `X₂ q`, `X₃ q` with maps

`⋯ ⟶ X₃ (q + 1) ⟶ X₁ q ⟶ X₂ q ⟶ X₃ q ⟶ X₁ (q - 1) ⟶ ⋯`

whose consecutive composites vanish form a single `ℤ`-graded chain complex
`ChainComplex.interleave`, with `X₁ q` in degree `3q + 2`, `X₂ q` in degree `3q + 1` and
`X₃ q` in degree `3q`. Its exactness in each degree is exactly the exactness of the original
sequence at the corresponding object (`ChainComplex.exactAt_interleave_iff_of_eq_three_mul_add_two`
and its two companions), so it is acyclic exactly when that sequence is exact everywhere.

The main example is the long exact homology sequence of a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `ℤ`-graded chain complexes in an abelian category:

`⋯ ⟶ Hᵢ₊₁(S.X₃) ⟶ Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃) ⟶ Hᵢ₋₁(S.X₁) ⟶ ⋯`.

`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex` is this sequence regarded as an
acyclic chain complex (`CategoryTheory.ShortComplex.ShortExact.acyclic_homologySequenceComplex`),
with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)`, `Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1`, `3i`. For complexes of
vector spaces with chosen bases of the homology groups, this is the based acyclic complex whose
Reidemeister torsion enters Milnor's formula for the torsion of a short exact sequence of
complexes that need not be acyclic (Milnor, *Whitehead torsion*, Theorem 3.2).

The degree of an object is not a definitional function of the indices `q`, since `(3 * q + 2) / 3`
only equals `q` propositionally. The objects in each degree are therefore identified with the
original ones by the isomorphisms `ChainComplex.interleave.XIso₁`, `XIso₂` and `XIso₃`, which take
the degree as an argument together with an equation fixing it, and the differentials are described
through them.

## Main declarations

* `ChainComplex.interleave`: the chain complex interleaving the three families.
* `ChainComplex.interleave_d_eq_of_eq_three_mul_add_two` and its two companions: the
  differentials are `δ`, `f` and `g`, up to the identifications of the objects.
* `ChainComplex.exactAt_interleave_iff_of_eq_three_mul_add_two` and its two companions:
  exactness in each degree.
* `ChainComplex.acyclic_interleave_iff`: the complex is acyclic exactly when the sequence is
  exact at every object.
* `CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`: the long exact homology
  sequence of a short exact sequence of chain complexes, and
  `CategoryTheory.ShortComplex.ShortExact.acyclic_homologySequenceComplex`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Appendix A.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace ChainComplex

variable {C : Type*} [Category* C]
  {X₁ X₂ X₃ : ℤ → C} {f : ∀ q, X₁ q ⟶ X₂ q} {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q}

namespace interleave

/-! The objects and differentials are built before the complex exists, so the identifications
`objIso₁`, `objIso₂` and `objIso₃` used to define the differential are stated for `obj`. The
public isomorphisms `XIso₁`, `XIso₂` and `XIso₃` below are the same isomorphisms, stated for the
terms of `ChainComplex.interleave`. -/

variable (X₁ X₂ X₃) in
/-- The object in degree `n`: `X₃ q`, `X₂ q` or `X₁ q` according as `n = 3q`, `3q + 1` or
`3q + 2`. -/
private def obj (n : ℤ) : C :=
  if n % 3 = 0 then X₃ (n / 3) else if n % 3 = 1 then X₂ (n / 3) else X₁ (n / 3)

variable (X₁ X₂ X₃) in
private def objIso₁ (n q : ℤ) (h : n = 3 * q + 2) : obj X₁ X₂ X₃ n ≅ X₁ q :=
  eqToIso <| by
    have h₁ : n % 3 = 2 := by omega
    have h₂ : n / 3 = q := by omega
    simp [obj, h₁, h₂]

variable (X₁ X₂ X₃) in
private def objIso₂ (n q : ℤ) (h : n = 3 * q + 1) : obj X₁ X₂ X₃ n ≅ X₂ q :=
  eqToIso <| by
    have h₁ : n % 3 = 1 := by omega
    have h₂ : n / 3 = q := by omega
    simp [obj, h₁, h₂]

variable (X₁ X₂ X₃) in
private def objIso₃ (n q : ℤ) (h : n = 3 * q) : obj X₁ X₂ X₃ n ≅ X₃ q :=
  eqToIso <| by
    have h₁ : n % 3 = 0 := by omega
    have h₂ : n / 3 = q := by omega
    simp [obj, h₁, h₂]

variable (f g δ) in
/-- The differential from degree `n + 1` to degree `n`: `g`, `f` or `δ` according as `n = 3q`,
`3q + 1` or `3q + 2`. -/
private def dif (n : ℤ) : obj X₁ X₂ X₃ (n + 1) ⟶ obj X₁ X₂ X₃ n :=
  if _ : n % 3 = 0 then
    (objIso₂ X₁ X₂ X₃ (n + 1) (n / 3) (by omega)).hom ≫ g (n / 3) ≫
      (objIso₃ X₁ X₂ X₃ n (n / 3) (by omega)).inv
  else if _ : n % 3 = 1 then
    (objIso₁ X₁ X₂ X₃ (n + 1) (n / 3) (by omega)).hom ≫ f (n / 3) ≫
      (objIso₂ X₁ X₂ X₃ n (n / 3) (by omega)).inv
  else
    (objIso₃ X₁ X₂ X₃ (n + 1) (n / 3 + 1) (by omega)).hom ≫ δ (n / 3) ≫
      (objIso₁ X₁ X₂ X₃ n (n / 3) (by omega)).inv

private theorem dif_eq₁ {n q : ℤ} (h : n = 3 * q + 2) :
    dif f g δ n = (objIso₃ X₁ X₂ X₃ (n + 1) (q + 1) (by omega)).hom ≫ δ q ≫
      (objIso₁ X₁ X₂ X₃ n q h).inv := by
  obtain rfl : n / 3 = q := by omega
  rw [dif, dite_eq_right (by omega), dite_eq_right (by omega)]

private theorem dif_eq₂ {n q : ℤ} (h : n = 3 * q + 1) :
    dif f g δ n = (objIso₁ X₁ X₂ X₃ (n + 1) q (by omega)).hom ≫ f q ≫
      (objIso₂ X₁ X₂ X₃ n q h).inv := by
  obtain rfl : n / 3 = q := by omega
  rw [dif, dite_eq_right (by omega), dite_eq_left (by omega)]

private theorem dif_eq₃ {n q : ℤ} (h : n = 3 * q) :
    dif f g δ n = (objIso₂ X₁ X₂ X₃ (n + 1) q (by omega)).hom ≫ g q ≫
      (objIso₃ X₁ X₂ X₃ n q h).inv := by
  obtain rfl : n / 3 = q := by omega
  rw [dif, dite_eq_left (by omega)]

variable [HasZeroMorphisms C]

private theorem dif_comp_dif (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
    (hδf : ∀ q, δ q ≫ f q = 0) (n : ℤ) : dif f g δ (n + 1) ≫ dif f g δ n = 0 := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 :=
    ⟨n / 3, by omega⟩
  · rw [dif_eq₂ (q := q) (by omega), dif_eq₃ hq]
    simp [reassoc_of% hfg q]
  · rw [dif_eq₁ (q := q) (by omega), dif_eq₂ hq]
    simp [reassoc_of% hδf q]
  · rw [dif_eq₃ (q := q + 1) (by omega), dif_eq₁ hq]
    simp [reassoc_of% hgδ q]

end interleave

variable [HasZeroMorphisms C]

variable (X₁ X₂ X₃ f g δ) in
/-- The `ℤ`-graded chain complex `⋯ ⟶ X₃ (q + 1) ⟶ X₁ q ⟶ X₂ q ⟶ X₃ q ⟶ X₁ (q - 1) ⟶ ⋯`, with
`X₁ q`, `X₂ q` and `X₃ q` in degrees `3q + 2`, `3q + 1` and `3q`, whose differentials out of
degrees `3q + 3`, `3q + 2` and `3q + 1` are `δ q`, `f q` and `g q`. -/
def interleave (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
    (hδf : ∀ q, δ q ≫ f q = 0) : ChainComplex C ℤ :=
  ChainComplex.of (interleave.obj X₁ X₂ X₃) (interleave.dif f g δ)
    (interleave.dif_comp_dif hfg hgδ hδf)

variable (hfg : ∀ q, f q ≫ g q = 0) (hgδ : ∀ q, g (q + 1) ≫ δ q = 0)
  (hδf : ∀ q, δ q ≫ f q = 0)

namespace interleave

/-- In degree `n = 3q + 2` the object of `ChainComplex.interleave` is `X₁ q`. -/
def XIso₁ (n q : ℤ) (h : n = 3 * q + 2) : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n ≅ X₁ q :=
  objIso₁ X₁ X₂ X₃ n q h

/-- In degree `n = 3q + 1` the object of `ChainComplex.interleave` is `X₂ q`. -/
def XIso₂ (n q : ℤ) (h : n = 3 * q + 1) : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n ≅ X₂ q :=
  objIso₂ X₁ X₂ X₃ n q h

/-- In degree `n = 3q` the object of `ChainComplex.interleave` is `X₃ q`. -/
def XIso₃ (n q : ℤ) (h : n = 3 * q) : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n ≅ X₃ q :=
  objIso₃ X₁ X₂ X₃ n q h

end interleave

open interleave

/-- The differential of `ChainComplex.interleave` out of degree `3q + 3` is `δ q`. -/
theorem interleave_d_eq_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n =
      (XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).hom ≫ δ q ≫
        (XIso₁ hfg hgδ hδf n q h).inv := by
  exact (ChainComplex.of_d _ _ n).trans (dif_eq₁ h)

/-- The differential of `ChainComplex.interleave` out of degree `3q + 2` is `f q`. -/
theorem interleave_d_eq_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n =
      (XIso₁ hfg hgδ hδf (n + 1) q (by omega)).hom ≫ f q ≫
        (XIso₂ hfg hgδ hδf n q h).inv := by
  exact (ChainComplex.of_d _ _ n).trans (dif_eq₂ h)

/-- The differential of `ChainComplex.interleave` out of degree `3q + 1` is `g q`. -/
theorem interleave_d_eq_of_eq_three_mul {n q : ℤ} (h : n = 3 * q) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n =
      (XIso₂ hfg hgδ hδf (n + 1) q (by omega)).hom ≫ g q ≫
        (XIso₃ hfg hgδ hδf n q h).inv := by
  exact (ChainComplex.of_d _ _ n).trans (dif_eq₃ h)

/-- `ChainComplex.interleave` is exact in degree `3q + 2` exactly when the sequence is exact at
`X₁ q`. -/
theorem exactAt_interleave_iff_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).ExactAt n ↔
      (ShortComplex.mk (δ q) (f q) (hδf q)).Exact := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (m + 1 + 1) (m + 1) m (by simp) (by simp)]
  refine ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (XIso₃ hfg hgδ hδf (m + 1 + 1) (q + 1) (by omega)) (XIso₁ hfg hgδ hδf (m + 1) q h)
    (XIso₂ hfg hgδ hδf m q (by omega)) ?_ ?_)
  · simp [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf h]
  · simp [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf (n := m) (q := q) (by omega)]

/-- `ChainComplex.interleave` is exact in degree `3q + 1` exactly when the sequence is exact at
`X₂ q`. -/
theorem exactAt_interleave_iff_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).ExactAt n ↔
      (ShortComplex.mk (f q) (g q) (hfg q)).Exact := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (m + 1 + 1) (m + 1) m (by simp) (by simp)]
  refine ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (XIso₁ hfg hgδ hδf (m + 1 + 1) q (by omega)) (XIso₂ hfg hgδ hδf (m + 1) q h)
    (XIso₃ hfg hgδ hδf m q (by omega)) ?_ ?_)
  · simp [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf h]
  · simp [interleave_d_eq_of_eq_three_mul hfg hgδ hδf (n := m) (q := q) (by omega)]

/-- `ChainComplex.interleave` is exact in degree `3q + 3` exactly when the sequence is exact at
`X₃ (q + 1)`. -/
theorem exactAt_interleave_iff_of_eq_three_mul_add_three {n q : ℤ} (h : n = 3 * q + 3) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).ExactAt n ↔
      (ShortComplex.mk (g (q + 1)) (δ q) (hgδ q)).Exact := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (m + 1 + 1) (m + 1) m (by simp) (by simp)]
  refine ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (XIso₂ hfg hgδ hδf (m + 1 + 1) (q + 1) (by omega))
    (XIso₃ hfg hgδ hδf (m + 1) (q + 1) (by omega)) (XIso₁ hfg hgδ hδf m q (by omega)) ?_ ?_)
  · simp [interleave_d_eq_of_eq_three_mul hfg hgδ hδf (n := m + 1) (q := q + 1) (by omega)]
  · simp [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf (n := m) (q := q) (by omega)]

/-- `ChainComplex.interleave` is acyclic exactly when the sequence
`⋯ ⟶ X₃ (q + 1) ⟶ X₁ q ⟶ X₂ q ⟶ X₃ q ⟶ ⋯` is exact at every object. -/
theorem acyclic_interleave_iff :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic ↔
      (∀ q, (ShortComplex.mk (δ q) (f q) (hδf q)).Exact) ∧
        (∀ q, (ShortComplex.mk (f q) (g q) (hfg q)).Exact) ∧
          ∀ q, (ShortComplex.mk (g (q + 1)) (δ q) (hgδ q)).Exact := by
  refine ⟨fun hK ↦ ⟨fun q ↦ ?_, fun q ↦ ?_, fun q ↦ ?_⟩, fun ⟨h₁, h₂, h₃⟩ n ↦ ?_⟩
  · exact (exactAt_interleave_iff_of_eq_three_mul_add_two hfg hgδ hδf rfl).1 (hK _)
  · exact (exactAt_interleave_iff_of_eq_three_mul_add_one hfg hgδ hδf rfl).1 (hK _)
  · exact (exactAt_interleave_iff_of_eq_three_mul_add_three hfg hgδ hδf rfl).1 (hK _)
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q + 3 :=
    ⟨(n - 1) / 3, by omega⟩
  · exact (exactAt_interleave_iff_of_eq_three_mul_add_two hfg hgδ hδf hq).2 (h₁ q)
  · exact (exactAt_interleave_iff_of_eq_three_mul_add_one hfg hgδ hδf hq).2 (h₂ q)
  · exact (exactAt_interleave_iff_of_eq_three_mul_add_three hfg hgδ hδf hq).2 (h₃ q)

end ChainComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type*} [Category* C] [Abelian C] {S : ShortComplex (ChainComplex C ℤ)}
  (hS : S.ShortExact)

/-- The long exact homology sequence
`⋯ ⟶ Hᵢ₊₁(S.X₃) ⟶ Hᵢ(S.X₁) ⟶ Hᵢ(S.X₂) ⟶ Hᵢ(S.X₃) ⟶ Hᵢ₋₁(S.X₁) ⟶ ⋯` of a short exact sequence of
`ℤ`-graded chain complexes, regarded as a chain complex with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and `Hᵢ(S.X₃)`
in degrees `3i + 2`, `3i + 1` and `3i`. Its differentials are the maps induced by `S.f` and `S.g`
and the connecting homomorphisms `hS.δ`. It is reducible, so the API of `ChainComplex.interleave`
applies to it directly. -/
abbrev homologySequenceComplex : ChainComplex C ℤ :=
  ChainComplex.interleave (fun i ↦ S.X₁.homology i) (fun i ↦ S.X₂.homology i)
    (fun i ↦ S.X₃.homology i) (fun i ↦ HomologicalComplex.homologyMap S.f i)
    (fun i ↦ HomologicalComplex.homologyMap S.g i)
    (fun i ↦ hS.δ (i + 1) i rfl)
    (fun i ↦ by
      rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])
    (fun i ↦ hS.comp_δ (i + 1) i rfl) (fun i ↦ hS.δ_comp (i + 1) i rfl)

/-- The long exact homology sequence of a short exact sequence of chain complexes is acyclic. -/
theorem acyclic_homologySequenceComplex : hS.homologySequenceComplex.Acyclic :=
  (ChainComplex.acyclic_interleave_iff _ _ _).2
    ⟨fun i ↦ hS.homology_exact₁ (i + 1) i rfl, fun i ↦ hS.homology_exact₂ i,
      fun i ↦ hS.homology_exact₃ (i + 1) i rfl⟩

end CategoryTheory.ShortComplex.ShortExact
