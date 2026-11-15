/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Reindex
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
public import TauCeti.CategoryTheory.Subobject.Cokernel

/-!
# Classical indexing of the spectral sequence of a filtered complex

The spectral sequence `CochainComplex.spectralSequence` of an increasing filtration `F` of a
cochain complex `K` is Mathlib's spectral sequence of a spectral object for the recipe
`coreE₂Cohomological`: its first page is numbered `2`, and the object at `(a, b)` on it is
`H^{a+b}(F_{b+1}/F_b)`. This file writes it in the two classical `E₁` indexings, by reindexing
(`CategoryTheory.SpectralSequence.reindex`) along a shift of the pages by `1` and an affine
bijection of `ℤ × ℤ`.

* **Decreasing filtrations of cochain complexes.** For a decreasing filtration `F^p` of `K`,
  `CochainComplex.decreasingFiltrationSpectralSequence F hF` is a cohomological spectral sequence
  (`CategoryTheory.CohomologicalSpectralSequence`) starting on page `1`, with differentials
  `d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`, and with
  `E₁^{p,q} ≅ H^{p+q}(F^p/F^{p+1})`
  (`CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso`). It is the spectral
  sequence of the increasing filtration `G_t = F^{-t}`, whose page `r + 1` has at
  `(2p + q + 1, -p - 1)` the object `E_r^{p,q}`.
* **Increasing filtrations of chain complexes.** A chain complex is regarded as a cochain complex
  `K` with `K^{-n} = C_n`. For an increasing filtration `F_p` of `K`,
  `CochainComplex.homologicalFiltrationSpectralSequence F hF` starts on page `1`, with
  differentials `d_r : E^r_{p,q} ⟶ E^r_{p-r,q+r-1}` and
  `E¹_{p,q} ≅ H_{p+q}(F_p/F_{p-1}) = H^{-(p+q)}(F_p/F_{p-1})`
  (`CochainComplex.homologicalFiltrationSpectralSequenceFirstPageXIso`). Its page `r` has at
  `(p, q)` the object of page `r + 1` of the spectral sequence of `F` at `(1 - 2p - q, p - 1)`.

For finite filtrations both converge strongly, to the graded pieces of the induced filtration of
the cohomology of `K`
(`CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite`,
`CochainComplex.homologicalFiltrationSpectralSequencePageXIsoGradedOfFinite`): in the decreasing
case `E_r^{p,q} ≅ F^p H^{p+q} / F^{p+1} H^{p+q}` and in the homological case
`E^r_{p,q} ≅ F_p H_{p+q} / F_{p-1} H_{p+q}`, once `r` is large compared with the length of the
filtration. For complexes of modules the same holds without a finite length, under the
degreewise vanishing and exhaustiveness hypotheses of
`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfExhaustive`
(`CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfExhaustive`,
`CochainComplex.homologicalFiltrationSpectralSequencePageXIsoGradedOfExhaustive`), which hold
for instance for a first-quadrant decreasing filtration (`F^0 = K` and `F^{n+1} K^n = 0`) on every
page `r` large compared with `p` and `q`.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Sections 5.4 and 5.5.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, Section 2.2.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}

/-! ### Decreasing filtrations -/

section Decreasing

/-- The bijection of `ℤ × ℤ` sending the bidegree `(p, q)` of the spectral sequence of a decreasing
filtration `F^p` to the bidegree `(2p + q + 1, -p - 1)` of the spectral sequence of the increasing
filtration `t ↦ F^{-t}`. -/
def decreasingFiltrationBidegreeEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun pq := (2 * pq.1 + pq.2 + 1, -pq.1 - 1)
  invFun ab := (-ab.2 - 1, ab.1 + 2 * ab.2 + 1)
  left_inv pq := by ext <;> dsimp <;> lia
  right_inv ab := by ext <;> dsimp <;> lia

@[simp]
lemma decreasingFiltrationBidegreeEquiv_apply (pq : ℤ × ℤ) :
    decreasingFiltrationBidegreeEquiv pq = (2 * pq.1 + pq.2 + 1, -pq.1 - 1) :=
  (rfl)

@[simp]
lemma decreasingFiltrationBidegreeEquiv_symm_apply (ab : ℤ × ℤ) :
    decreasingFiltrationBidegreeEquiv.symm ab = (-ab.2 - 1, ab.1 + 2 * ab.2 + 1) :=
  (rfl)

/-- The bijection `decreasingFiltrationBidegreeEquiv` carries the differentials `(r, 1 - r)` of the
`r`th page of a cohomological spectral sequence to the differentials `(r + 1, -r)` of page `r + 1`
of the spectral sequence of a filtered complex. -/
lemma decreasingFiltrationBidegreeEquiv_rel_iff (r : ℤ) (i j : ℤ × ℤ) :
    (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel i j ↔
      (ComplexShape.up' (⟨r + 1, 1 - (r + 1)⟩ : ℤ × ℤ)).Rel (decreasingFiltrationBidegreeEquiv i)
        (decreasingFiltrationBidegreeEquiv j) := by
  obtain ⟨p, q⟩ := i
  obtain ⟨p', q'⟩ := j
  simp only [ComplexShape.up', decreasingFiltrationBidegreeEquiv_apply, Prod.mk_add_mk,
    Prod.mk.injEq]
  lia

variable (F : ℤ → Subobject K) (hF : Antitone F)

/-- The **spectral sequence of a decreasing filtration** `F^p` of a cochain complex, in the
classical cohomological indexing: it starts on page `1`, its differentials are
`d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`, and `E₁^{p,q} = H^{p+q}(F^p/F^{p+1})`. It is the spectral
sequence of the increasing filtration `t ↦ F^{-t}`, reindexed. -/
noncomputable def decreasingFiltrationSpectralSequence : CohomologicalSpectralSequence C 1 :=
  (spectralSequence (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))).reindex 1
    decreasingFiltrationBidegreeEquiv decreasingFiltrationBidegreeEquiv_rel_iff (by lia)

/-- The object at `(p, q)` on page `r` of the spectral sequence of a decreasing filtration `F` is
the object at `(2p + q + 1, -p - 1)` on page `r + 1` of the spectral sequence of the increasing
filtration `t ↦ F^{-t}`. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIso (r r' : ℤ) (hr : 1 ≤ r)
    (hr' : r + 1 = r') (p q a b : ℤ) (ha : a = 2 * p + q + 1) (hb : b = -p - 1) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      ((spectralSequence (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))).page r'
        (by lia)).X (a, b) :=
  SpectralSequence.reindexPageXIso _ _ _ _ _ r r' hr hr' (p, q) (a, b) (by simp [ha, hb])

/-- **The first page of the spectral sequence of a decreasing filtration.** The object at
`(p, q)` is the cohomology `H^{p+q}(F^p/F^{p+1})` of the graded piece `F^p/F^{p+1}`. -/
noncomputable def decreasingFiltrationSpectralSequenceFirstPageXIso (p q : ℤ) :
    ((decreasingFiltrationSpectralSequence F hF).page 1).X (p, q) ≅
      (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by lia)))).homology (p + q) :=
  decreasingFiltrationSpectralSequencePageXIso F hF 1 2 le_rfl rfl p q _ _ rfl rfl ≪≫
    spectralSequenceFirstPageXIsoCokernel _ (2 * p + q + 1, -p - 1) (-p - 1) (-p) rfl (by lia)
      (p + q) (by dsimp; lia) ≪≫
    (HomologicalComplex.homologyFunctor C _ (p + q)).mapIso
      (cokernelFiltrationFunctorMapIso _ _ _ ≪≫
        Subobject.cokernelOfLEIsoOfEq (by simp [add_comm]) (by simp) _ _)

/-- **Strong convergence of the spectral sequence of a finite decreasing filtration.** If
`F^a = ⊥` and `F^b = ⊤`, then on every page `r ≥ 1` with `a ≤ p + r` and `p - r + 1 ≤ b`, the object
at `(p, q)` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of
`H^{p+q}(K)`, whose `p`th piece is the image of `H^{p+q}(F^p) ⟶ H^{p+q}(K)`; in the indexing of the
increasing filtration `t ↦ F^{-t}` this is the piece at `-p`. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite {a b : ℤ}
    (ha : F a = ⊥) (hb : F b = ⊤) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hra : a ≤ p + r)
    (hrb : p - r + 1 ≤ b) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (spectralObject (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))) (-p - 1)
        (p + q)) :=
  decreasingFiltrationSpectralSequencePageXIso F hF r (r + 1) hr rfl p q _ _ rfl rfl ≪≫
    filtrationSpectralSequencePageXIsoGradedOfFinite _ (hF.comp fun _ _ h ↦ neg_le_neg h)
      (a := -a) (b := -b) (by simpa using ha) (by simpa using hb) (r + 1) (by lia)
      (2 * p + q + 1, -p - 1) (by dsimp; lia) (by dsimp; lia) ≪≫
    eqToIso (by dsimp only; rw [show 2 * p + q + 1 + (-p - 1) = p + q by lia])

end Decreasing

/-! ### Homological indexing -/

section Homological

/-- The bijection of `ℤ × ℤ` sending the bidegree `(p, q)` of the homological spectral sequence of
an increasing filtration `F_p` to the bidegree `(1 - 2p - q, p - 1)` of its spectral sequence in
the indexing of `CochainComplex.spectralSequence`. -/
def homologicalFiltrationBidegreeEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun pq := (1 - 2 * pq.1 - pq.2, pq.1 - 1)
  invFun ab := (ab.2 + 1, -ab.1 - 2 * ab.2 - 1)
  left_inv pq := by ext <;> dsimp <;> lia
  right_inv ab := by ext <;> dsimp <;> lia

@[simp]
lemma homologicalFiltrationBidegreeEquiv_apply (pq : ℤ × ℤ) :
    homologicalFiltrationBidegreeEquiv pq = (1 - 2 * pq.1 - pq.2, pq.1 - 1) :=
  (rfl)

@[simp]
lemma homologicalFiltrationBidegreeEquiv_symm_apply (ab : ℤ × ℤ) :
    homologicalFiltrationBidegreeEquiv.symm ab = (ab.2 + 1, -ab.1 - 2 * ab.2 - 1) :=
  (rfl)

/-- The bijection `homologicalFiltrationBidegreeEquiv` carries the differentials `(-r, r - 1)` of
the `r`th page of a homological spectral sequence to the differentials `(r + 1, -r)` of page
`r + 1` of the spectral sequence of a filtered complex. -/
lemma homologicalFiltrationBidegreeEquiv_rel_iff (r : ℤ) (i j : ℤ × ℤ) :
    (ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)).Rel i j ↔
      (ComplexShape.up' (⟨r + 1, 1 - (r + 1)⟩ : ℤ × ℤ)).Rel
        (homologicalFiltrationBidegreeEquiv i) (homologicalFiltrationBidegreeEquiv j) := by
  obtain ⟨p, q⟩ := i
  obtain ⟨p', q'⟩ := j
  simp only [ComplexShape.up', homologicalFiltrationBidegreeEquiv_apply, Prod.mk_add_mk,
    Prod.mk.injEq]
  lia

variable (F : ℤ → Subobject K) (hF : Monotone F)

/-- The **homological spectral sequence of an increasing filtration** `F_p` of a chain complex,
regarded as a cochain complex `K` with `K^{-n} = C_n`: it starts on page `1`, its differentials
are `d_r : E^r_{p,q} ⟶ E^r_{p-r,q+r-1}`, and `E¹_{p,q} = H_{p+q}(F_p/F_{p-1})`, the cohomology of
`F_p/F_{p-1}` in degree `-(p+q)`. -/
noncomputable def homologicalFiltrationSpectralSequence :
    SpectralSequence C (fun r ↦ ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) 1 :=
  (spectralSequence (filtrationFunctor F hF)).reindex 1 homologicalFiltrationBidegreeEquiv
    homologicalFiltrationBidegreeEquiv_rel_iff (by lia)

/-- The object at `(p, q)` on page `r` of the homological spectral sequence of an increasing
filtration `F` is the object at `(1 - 2p - q, p - 1)` on page `r + 1` of its spectral sequence in
the indexing of `CochainComplex.spectralSequence`. -/
noncomputable def homologicalFiltrationSpectralSequencePageXIso (r r' : ℤ) (hr : 1 ≤ r)
    (hr' : r + 1 = r') (p q a b : ℤ) (ha : a = 1 - 2 * p - q) (hb : b = p - 1) :
    ((homologicalFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      ((spectralSequence (filtrationFunctor F hF)).page r' (by lia)).X (a, b) :=
  SpectralSequence.reindexPageXIso _ _ _ _ _ r r' hr hr' (p, q) (a, b) (by simp [ha, hb])

/-- **The first page of the homological spectral sequence of an increasing filtration.** The
object at `(p, q)` is the homology `H_{p+q}(F_p/F_{p-1})` of the graded piece `F_p/F_{p-1}`, that
is its cohomology in degree `-(p+q)`. -/
noncomputable def homologicalFiltrationSpectralSequenceFirstPageXIso (p q : ℤ) :
    ((homologicalFiltrationSpectralSequence F hF).page 1).X (p, q) ≅
      (cokernel (Subobject.ofLE (F (p - 1)) (F p) (hF (by lia)))).homology (-(p + q)) :=
  homologicalFiltrationSpectralSequencePageXIso F hF 1 2 le_rfl rfl p q _ _ rfl rfl ≪≫
    spectralSequenceFirstPageXIsoCokernel _ (1 - 2 * p - q, p - 1) (p - 1) p rfl (by lia)
      (-(p + q)) (by dsimp; lia) ≪≫
    (HomologicalComplex.homologyFunctor C _ (-(p + q))).mapIso
      (cokernelFiltrationFunctorMapIso _ _ _ ≪≫
        Subobject.cokernelOfLEIsoOfEq (filtrationEInt_coe F (p - 1)) (filtrationEInt_coe F p) _ _)

/-- **Strong convergence of the homological spectral sequence of a finite filtration.** If
`F_a = ⊥` and `F_b = ⊤`, then on every page `r ≥ 1` with `p - r ≤ a` and `b ≤ p + r - 1`, the object
at `(p, q)` is the graded piece `F_p H_{p+q} / F_{p-1} H_{p+q}` of the induced filtration of
`H_{p+q}(K) = H^{-(p+q)}(K)`, whose `p`th piece is the image of
`H^{-(p+q)}(F_p) ⟶ H^{-(p+q)}(K)`. -/
noncomputable def homologicalFiltrationSpectralSequencePageXIsoGradedOfFinite {a b : ℤ}
    (ha : F a = ⊥) (hb : F b = ⊤) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hra : p - r ≤ a)
    (hrb : b ≤ p + r - 1) :
    ((homologicalFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap (p - 1)
        (-(p + q))) :=
  homologicalFiltrationSpectralSequencePageXIso F hF r (r + 1) hr rfl p q _ _ rfl rfl ≪≫
    filtrationSpectralSequencePageXIsoGradedOfFinite F hF ha hb (r + 1) (by lia)
      (1 - 2 * p - q, p - 1) (by dsimp; lia) (by dsimp; lia) ≪≫
    eqToIso (by dsimp only; rw [show 1 - 2 * p - q + (p - 1) = -(p + q) by lia])

end Homological

/-! ### Exhaustive filtrations of complexes of modules -/

section ModuleCat

variable {R : Type*} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- **Strong convergence of the spectral sequence of a decreasing filtration**, without a finite
length. Let `F` be a decreasing filtration of a complex of modules. Suppose that every element of
`K^{p+q-1}` lies in some `F^j`, that `H^{p+q+1}(F^{p+r})` vanishes, and that the graded pieces
`F^j/F^{j+1}` have vanishing `H^{p+q-1}` for all `j ≤ p - r`. Then the object at `(p, q)` on page
`r ≥ 1` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of
`H^{p+q}(K)`. For a first-quadrant filtration, `F^0 = K` and `F^{n+1} K^n = 0`, the hypotheses hold
for every `r` large compared with `p` and `q`. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIsoGradedOfExhaustive
    (F : ℤ → Subobject K) (hF : Antitone F) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hex : ∀ x : K.X (p + q - 1), ∃ j, x ∈ LinearMap.range ((F j).arrow.f (p + q - 1)).hom)
    (h₀ : IsZero ((F (p + r) : CochainComplex (ModuleCat R) ℤ).homology (p + q + 1)))
    (h₃ : ∀ j, j ≤ p - r →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q - 1))) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (spectralObject (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))) (-p - 1)
        (p + q)) :=
  decreasingFiltrationSpectralSequencePageXIso F hF r (r + 1) hr rfl p q _ _ rfl rfl ≪≫
    filtrationSpectralSequencePageXIsoGradedOfExhaustive _ (hF.comp fun _ _ h ↦ neg_le_neg h)
      (r + 1) (by lia) (2 * p + q + 1, -p - 1)
      (by
        dsimp only
        rw [show 2 * p + q + 1 + (-p - 1) - 1 = p + q - 1 by lia]
        intro x
        obtain ⟨j, hj⟩ := hex x
        refine ⟨-j, ?_⟩
        rw [Function.comp_apply, neg_neg]
        exact hj)
      (by
        dsimp only
        rw [show -p - 1 - (r + 1) + 2 = -(p + r) by lia,
          show 2 * p + q + 1 + (-p - 1) + 1 = p + q + 1 by lia]
        simpa using h₀)
      (fun i hi ↦ by
        dsimp only at hi ⊢
        rw [show 2 * p + q + 1 + (-p - 1) - 1 = p + q - 1 by lia]
        exact (h₃ (-i - 1) (by lia)).of_iso
          ((HomologicalComplex.homologyFunctor _ _ (p + q - 1)).mapIso
            (Subobject.cokernelOfLEIsoOfEq (by rw [Function.comp_apply]; congr 1; lia)
              (by rw [Function.comp_apply]; congr 1; lia) _ _))) ≪≫
    eqToIso (by dsimp only; rw [show 2 * p + q + 1 + (-p - 1) = p + q by lia])

/-- **Strong convergence of the homological spectral sequence of an increasing filtration**,
without a finite length. Let `F` be an increasing filtration of a complex of modules, read as a
chain complex with `K^{-n} = C_n`. Suppose that every element of `C_{p+q+1}` lies in some `F_j`,
that `H_{p+q-1}(F_{p-r})` vanishes, and that the graded pieces `F_{j+1}/F_j` have vanishing
`H_{p+q+1}` for all `j ≥ p + r - 1`. Then the object at `(p, q)` on page `r ≥ 1` is the graded
piece `F_p H_{p+q} / F_{p-1} H_{p+q}` of the induced filtration of `H_{p+q}(K)`. -/
noncomputable def homologicalFiltrationSpectralSequencePageXIsoGradedOfExhaustive
    (F : ℤ → Subobject K) (hF : Monotone F) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hex : ∀ x : K.X (-(p + q) - 1),
      ∃ j, x ∈ LinearMap.range ((F j).arrow.f (-(p + q) - 1)).hom)
    (h₀ : IsZero ((F (p - r) : CochainComplex (ModuleCat R) ℤ).homology (-(p + q) + 1)))
    (h₃ : ∀ j, p + r - 1 ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F j) (F (j + 1)) (hF (by lia)))).homology
        (-(p + q) - 1))) :
    ((homologicalFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap (p - 1)
        (-(p + q))) :=
  homologicalFiltrationSpectralSequencePageXIso F hF r (r + 1) hr rfl p q _ _ rfl rfl ≪≫
    filtrationSpectralSequencePageXIsoGradedOfExhaustive F hF (r + 1) (by lia)
      (1 - 2 * p - q, p - 1)
      (by
        dsimp only
        rw [show 1 - 2 * p - q + (p - 1) - 1 = -(p + q) - 1 by lia]
        exact hex)
      (by
        dsimp only
        rw [show p - 1 - (r + 1) + 2 = p - r by lia,
          show 1 - 2 * p - q + (p - 1) + 1 = -(p + q) + 1 by lia]
        exact h₀)
      (fun i hi ↦ by
        dsimp only at hi ⊢
        rw [show 1 - 2 * p - q + (p - 1) - 1 = -(p + q) - 1 by lia]
        exact h₃ i (by lia)) ≪≫
    eqToIso (by dsimp only; rw [show 1 - 2 * p - q + (p - 1) = -(p + q) by lia])

end ModuleCat

end CochainComplex
