/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.CompleteFiltration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.CategoryTheory.Subobject.Cokernel

/-!
# Convergence for complete filtrations

Let `F` be an increasing filtration of a cochain complex of modules `K`. The convergence theorems
of `TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive` control the top of the
filtration through exhaustiveness, but at the bottom they need the stages `F_a` themselves to be
acyclic in the relevant degrees, as happens when `F_a = ⊥`. Decreasing filtrations of cochain
complexes are often not of this kind: in the filtration of the singular cochains of a space by
vanishing on the preimages of the skeleta of a CW base, no stage vanishes in any degree unless the
base is finite-dimensional, but the filtration is complete and separated, and its first page
vanishes below the horizontal axis. The acyclicity of a stage of a complete filtration whose
graded pieces are acyclic, `CochainComplex.isZero_homology_of_isCompleteFiltration_of_monotone`
and `CochainComplex.isZero_homology_of_isCompleteFiltration_of_antitone` in
`TauCeti.Algebra.Homology.CochainComplex.CompleteFiltration`, supplies the missing bottom
hypothesis. Completeness is Tau Ceti's `TauCeti.IsCompleteFiltration`, imposed degreewise on the
descending chain of submodules `F_{a-k}^n ⊆ K^n`, `k : ℕ`, the ranges of the inclusions of the
stages; in the top degree involved only separation is needed. Consequently:

* the filtration of the abutment vanishes at `a`
  (`CochainComplex.isZero_filtrationAbutmentFiltration_of_isCompleteFiltration`);
* the spectral sequence of a complete exhaustive filtration converges strongly to the graded
  pieces of the induced filtration of the cohomology
  (`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfComplete`,
  `CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfComplete`), in particular
  for a complete first-quadrant decreasing filtration on every page `r` with `p < r` and
  `q + 1 < r`
  (`CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant`);
* a morphism of complete exhaustive filtered complexes which is an isomorphism on some page
  induces an isomorphism in cohomology
  (`CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page_of_complete`).

These are the cases of Weibel's Complete Convergence Theorem 5.5.10 in which the first page
vanishes in the relevant degrees beyond a bound, such as first-quadrant spectral sequences.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.10.
-/

public section

open CategoryTheory Limits Abelian.SpectralObject

namespace CochainComplex

universe v

variable {R : Type*} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- **The filtration of the abutment of a complete filtration is separated.** Under the hypotheses
of `CochainComplex.isZero_homology_of_isCompleteFiltration_of_monotone` in degrees `n - 1` and
`n`, the `a`th piece `F_a H^n` of the filtration of the abutment `H^n(K)` vanishes. -/
lemma isZero_filtrationAbutmentFiltration_of_isCompleteFiltration (F : ℤ → Subobject K)
    (hF : Monotone F) {a n' n : ℤ} (hn : n' + 1 = n)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f n').hom)
    (hsep : ∀ z, (∀ k : ℕ, z ∈ LinearMap.range ((F (a - k)).arrow.f n).hom) → z = 0)
    (h : ∀ i, i < a →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        n)) :
    IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration a n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _ (isZero_spectralObject_H_bot F hF a n
    (isZero_homology_of_isCompleteFiltration_of_monotone F hF hn hc₀ hsep h))

/-- **Strong convergence for a complete exhaustive filtration.** Let `pq = (p, q)` and
`n = p + q`. Suppose that every element of `K^{n-1}` lies in some `F_i`, that below `F_{q-r+2}`
the filtration is degreewise complete and separated in degree `n` and separated in degree `n + 1`,
and that the
graded pieces `F_{i+1}/F_i` have vanishing `H^{n+1}` for all `i < q - r + 2` and vanishing
`H^{n-1}` for all `i ≥ q + r - 1`. Then the object at `(p, q)` on page `r ≥ 2` is the graded piece
`F_{q+1} H^n / F_q H^n` of the filtration of the abutment `H^n(K)`. -/
noncomputable def filtrationSpectralSequencePageXIsoGradedOfComplete (F : ℤ → Subobject K)
    (hF : Monotone F) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (pq.2 - r + 2 - k)).arrow.f (pq.1 + pq.2)).hom)
    (hsep : ∀ z, (∀ k : ℕ, z ∈
      LinearMap.range ((F (pq.2 - r + 2 - k)).arrow.f (pq.1 + pq.2 + 1)).hom) → z = 0)
    (h₀ : ∀ i, i < pq.2 - r + 2 →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        (pq.1 + pq.2 + 1)))
    (h₃ : ∀ i, pq.2 + r - 1 ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        (pq.1 + pq.2 - 1))) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  filtrationSpectralSequencePageXIsoGradedOfExhaustive F hF r hr pq hex
    (isZero_homology_of_isCompleteFiltration_of_monotone F hF rfl hc₀ hsep h₀) h₃

/-- **The comparison theorem for complete exhaustive filtrations.** Let `α` be a morphism between
the functors of filtrations `F` of `K` and `G` of `L`, and let `n` be a degree. Suppose that both
filtrations are degreewise complete and separated in degrees `n - 1` and `n` and separated in
degree `n + 1`, that in degrees
`n - 1` and `n` every element of `K` and of `L` lies in some stage of the filtration, and that the
graded pieces of both filtrations have vanishing cohomology in degrees `n` and `n + 1` at all
indices `i < a`, and in degrees `n - 1` and `n` at all indices `i ≥ b`. If the morphism of
spectral sequences induced by `α` is an isomorphism on every object of some page `r ≥ 2`, then
`α.app ⊤` induces an isomorphism on `H^n`. -/
theorem isIso_homologyMap_of_isIso_spectralSequence_page_of_complete
    {L : CochainComplex (ModuleCat.{v} R) ℤ} (F : ℤ → Subobject K) (hF : Monotone F)
    (G : ℤ → Subobject L) (hG : Monotone G) (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG)
    (n : ℤ) {a b : ℤ}
    (hFc : ∀ m, n - 1 ≤ m → m ≤ n → ∀ i, TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (i - k)).arrow.f m).hom)
    (hGc : ∀ m, n - 1 ≤ m → m ≤ n → ∀ i, TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((G (i - k)).arrow.f m).hom)
    (hFs : ∀ i, ∀ z, (∀ k : ℕ, z ∈ LinearMap.range ((F (i - k)).arrow.f (n + 1)).hom) → z = 0)
    (hGs : ∀ i, ∀ z, (∀ k : ℕ, z ∈ LinearMap.range ((G (i - k)).arrow.f (n + 1)).hom) → z = 0)
    (hFex : ∀ m, n - 1 ≤ m → m ≤ n →
      ∀ x : K.X m, ∃ q, x ∈ LinearMap.range ((F q).arrow.f m).hom)
    (hGex : ∀ m, n - 1 ≤ m → m ≤ n →
      ∀ x : L.X m, ∃ q, x ∈ LinearMap.range ((G q).arrow.f m).hom)
    (hFa : ∀ m, n ≤ m → m ≤ n + 1 → ∀ i, i < a →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m))
    (hGa : ∀ m, n ≤ m → m ≤ n + 1 → ∀ i, i < a →
      IsZero ((cokernel (Subobject.ofLE (G i) (G (i + 1)) (hG (Int.le_add_one le_rfl)))).homology
        m))
    (hFb : ∀ m, n - 1 ≤ m → m ≤ n → ∀ i, b ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m))
    (hGb : ∀ m, n - 1 ≤ m → m ≤ n → ∀ i, b ≤ i →
      IsZero ((cokernel (Subobject.ofLE (G i) (G (i + 1)) (hG (Int.le_add_one le_rfl)))).homology
        m))
    (r : ℤ) (hr : 2 ≤ r)
    (h : ∀ pq, IsIso (((spectralSequenceMap coreE₂Cohomological
      (spectralObjectMap α)).hom r hr).f pq)) :
    IsIso (HomologicalComplex.homologyMap (α.app ⊤) n) :=
  isIso_homologyMap_of_isIso_spectralSequence_page_of_exhaustive F hF G hG α n (a := a) (b := b)
    (fun m hm₀ hm₁ i hi ↦ isZero_homology_of_isCompleteFiltration_of_monotone F hF
      (sub_add_cancel m 1) (hFc _ (by lia) (by lia) i) (by
        obtain hm | rfl : m ≤ n ∨ m = n + 1 := by lia
        exacts [(hFc m (by lia) hm i).eq_zero_of_forall_mem, hFs i])
      fun j hj ↦ hFa m hm₀ hm₁ j (by lia))
    (fun m hm₀ hm₁ i hi ↦ isZero_homology_of_isCompleteFiltration_of_monotone G hG
      (sub_add_cancel m 1) (hGc _ (by lia) (by lia) i) (by
        obtain hm | rfl : m ≤ n ∨ m = n + 1 := by lia
        exacts [(hGc m (by lia) hm i).eq_zero_of_forall_mem, hGs i])
      fun j hj ↦ hGa m hm₀ hm₁ j (by lia))
    hFex hGex hFb hGb r hr h

/-- **Strong convergence of the spectral sequence of a complete decreasing filtration.** Let `F` be
a decreasing filtration of a complex of modules. Suppose that every element of `K^{p+q-1}` lies in
some `F^j`, that above `F^{p+r}` the filtration is degreewise complete and separated in degree
`p + q` and separated in degree `p + q + 1`, and that the graded pieces `F^j/F^{j+1}` have
vanishing `H^{p+q+1}` for all `j ≥ p + r` and vanishing `H^{p+q-1}` for all `j ≤ p - r`. Then the
object at `(p, q)` on page `r ≥ 1` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the
induced filtration of `H^{p+q}(K)`. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIsoGradedOfComplete
    (F : ℤ → Subobject K) (hF : Antitone F) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hex : ∀ x : K.X (p + q - 1), ∃ j, x ∈ LinearMap.range ((F j).arrow.f (p + q - 1)).hom)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (p + r + k)).arrow.f (p + q)).hom)
    (hsep : ∀ z, (∀ k : ℕ, z ∈
      LinearMap.range ((F (p + r + k)).arrow.f (p + q + 1)).hom) → z = 0)
    (h₀ : ∀ j, p + r ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q + 1)))
    (h₃ : ∀ j, j ≤ p - r →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q - 1))) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (spectralObject (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))) (-p - 1)
        (p + q)) :=
  decreasingFiltrationSpectralSequencePageXIsoGradedOfExhaustive F hF r hr p q hex
    (isZero_homology_of_isCompleteFiltration_of_antitone F hF rfl hc₀ hsep h₀) h₃

/-- **Strong convergence for a complete first-quadrant decreasing filtration.** Let `F` be a
decreasing filtration of a complex of modules with `F^0 = K`, degreewise complete and separated
above each of its stages in every degree, whose first page vanishes below the horizontal axis:
`E₁^{j,n-j} = H^n(F^j/F^{j+1}) = 0` whenever `n < j`. Then on every page `r ≥ 1` with `p < r` and
`q + 1 < r`, the object at `(p, q)` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the
induced filtration of `H^{p+q}(K)`. No stage `F^j` need vanish in any degree, as for the
filtration of singular cochains by vanishing on the preimages of the skeleta of a CW base. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant
    (F : ℤ → Subobject K) (hF : Antitone F) (hF₀ : F 0 = ⊤)
    (hc : ∀ n j, TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (j + k)).arrow.f n).hom)
    (hq : ∀ j n, n < j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology n))
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hp : p < r) (hqr : q + 1 < r) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (spectralObject (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))) (-p - 1)
        (p + q)) :=
  have hF_top (j : ℤ) (hj : j ≤ 0) : F j = ⊤ := top_unique (hF₀ ▸ hF hj)
  decreasingFiltrationSpectralSequencePageXIsoGradedOfComplete F hF r hr p q
    (fun x ↦ ⟨0, (ModuleCat.epi_iff_surjective _).1 (by rw [hF₀]; infer_instance) x⟩)
    (hc _ _) (hc _ _).eq_zero_of_forall_mem (fun j hj ↦ hq j _ (by lia)) fun j hj ↦ by
      -- Below the filtration index `0` the graded pieces are `K/K = 0`.
      refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ _).mapIso
        (Subobject.cokernelOfLEIsoOfEq (hF_top (j + 1) (by lia)) (hF_top j (by lia)) _ le_rfl))
      have : IsIso (Subobject.ofLE (⊤ : Subobject K) ⊤ le_rfl) := by
        rw [Subobject.ofLE_refl]
        infer_instance
      exact (HomologicalComplex.acyclic_of_isZero _ (isZero_cokernel_of_epi _) _).isZero_homology

end CochainComplex
