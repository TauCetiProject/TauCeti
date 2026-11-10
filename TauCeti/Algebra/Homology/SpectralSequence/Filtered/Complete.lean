/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Subobject
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

/-!
# Convergence for complete filtrations

Let `F` be a filtration of a cochain complex of modules `K`. On the side where it is exhaustive,
the vanishing of the graded cohomology propagates to the quotients `K/F` by a directed-union
argument (`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive`). On the other side
there is no such argument: the stages need not reach `0`, and in each degree they may be nonzero
all the way down, as for the cochains of a Serre fibration filtered by the preimages of the
skeleta of the base. What replaces the finiteness there is *completeness*: in the decreasing
indexing, `K^n` is the inverse limit of the quotients `K^n/F^p K^n`, in the elementwise form of
`TauCeti.IsCompleteFiltration`.

The main result is that the stages of a complete filtration whose graded pieces have vanishing
cohomology are themselves acyclic
(`CochainComplex.isZero_homology_of_isCompleteFiltration`,
`CochainComplex.isZero_homology_of_antitone_of_isCompleteFiltration`). A cycle `x` of a stage is
a boundary modulo the next stage, by the vanishing of the graded cohomology; correcting it step by
step gives a series of elements going down the filtration, whose sum converges by completeness to
an element whose boundary is `x`, by separatedness (`TauCeti.IsCompleteFiltration.surjOn`).

Combined with the convergence statements for exhaustive filtrations, this gives the strong form of
Weibel's Complete Convergence Theorem 5.5.10 for complete exhaustive filtrations whose spectral
sequence is degreewise bounded:

* the filtration of the abutment `H^n(K)` vanishes from some stage on
  (`CochainComplex.isZero_filtrationAbutmentFiltration_of_isCompleteFiltration`);
* the objects on late enough pages are the graded pieces of the filtration of the abutment
  (`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfComplete`, and
  `CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfComplete` in the classical
  cohomological indexing of a decreasing filtration);
* a morphism of complete exhaustive filtered complexes which is an isomorphism on some page
  induces an isomorphism in cohomology
  (`CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page_of_complete`, Weibel's
  Comparison Theorem 5.5.11).

The degreewise boundedness of the spectral sequence is imposed through the vanishing of the
graded cohomology at all indices beyond a bound, as in the exhaustive case. The successive
approximation above is elementwise and uses no `lim¹` sequence. The weak convergence of a regular
spectral sequence that is not degreewise bounded is not treated here.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorems 5.5.10 and 5.5.11.
-/

public section

open CategoryTheory Limits Abelian.SpectralObject

namespace CochainComplex

universe v

variable {R : Type*} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}

section Increasing

variable (F : ℤ → Subobject K) (hF : Monotone F)

/-- **The stages of a complete filtration with vanishing graded cohomology are acyclic.** Let `F`
be an increasing filtration of a complex of modules `K`. Suppose that the stages `F_{a-k}`,
`k ≥ 0`, cut out a complete filtration of `K^{m-1}`, that the filtration of `K^m` is separated,
and that the graded pieces `F_{i+1}/F_i` have vanishing `H^m` for all `i < a`. Then
`H^m(F_a) = 0`. -/
theorem isZero_homology_of_isCompleteFiltration {a m : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (a - k)).arrow.f (m - 1)).hom)
    (hs : ∀ x : K.X m, (∀ i, x ∈ LinearMap.range ((F i).arrow.f m).hom) → x = 0)
    (h : ∀ i < a,
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m)) :
    IsZero ((F a : CochainComplex (ModuleCat R) ℤ).homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  -- Apply successive approximation to `d : K^{m-1} ⟶ Z^m`, the cycles of `K` in degree `m`, with
  -- the filtrations induced by the stages `F_{a-k}`.
  let Z := LinearMap.ker (K.d m (m + 1)).hom
  let f : K.X (m - 1) →ₗ[R] Z := (K.d (m - 1) m).hom.codRestrict Z fun y ↦ by
    simp [Z, ← ModuleCat.comp_apply]
  let G (k : ℕ) : Submodule R Z := (LinearMap.range ((F (a - k)).arrow.f m).hom).comap Z.subtype
  have hι (u : (F a : CochainComplex (ModuleCat R) ℤ).X m)
      (hu : (F a : CochainComplex (ModuleCat R) ℤ).d m (m + 1) u = 0) :
      K.d m (m + 1) ((F a).arrow.f m u) = 0 := by
    rw [HomologicalComplex.Hom.comm_apply, hu, map_zero]
  have e₀ : a - ((0 : ℕ) : ℤ) = a := by simp
  -- The image of the cycle `x` of `F_a` is a cycle of `K` lying in `F_a = F_{a-0}`.
  have hx₀ : (⟨(F a).arrow.f m x, hι x hx⟩ : Z) ∈ G 0 :=
    Submodule.mem_comap.2 (Subobject.range_arrow_f_hom_le (hF e₀.ge) m ⟨x, rfl⟩)
  obtain ⟨_, hy₀, hy⟩ := hc.surjOn (G := G)
    (fun z hz ↦ Subtype.ext <| hs z fun i ↦ Subobject.range_arrow_f_hom_le
      (hF (show a - ((a - i).toNat : ℕ) ≤ i by lia)) m (Submodule.mem_comap.1 (hz (a - i).toNat)))
    f (fun k ↦ by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.mem_comap.2 (Subobject.d_mem_range_arrow_f_hom _ (m - 1) m hy))
    (fun k z hz ↦ by
      have e : a - ((k + 1 : ℕ) : ℤ) + 1 = a - k := by lia
      obtain ⟨y, hy, hzy⟩ :=
        Subobject.exists_sub_d_mem_range_arrow_f_hom_of_isZero_homology_cokernel _
          (i := m - 1) (k := m + 1) (by simp) (by simp) (h (a - (k + 1 : ℕ)) (by lia))
          (e ▸ Submodule.mem_comap.1 hz) z.2
      exact ⟨y, e ▸ hy, Submodule.mem_comap.2 hzy⟩)
    hx₀
  obtain ⟨y, rfl⟩ := Subobject.range_arrow_f_hom_le (hF e₀.le) (m - 1) hy₀
  refine ⟨y, (ModuleCat.mono_iff_injective ((F a).arrow.f m)).1 inferInstance ?_⟩
  have hy := congrArg Subtype.val hy
  simp only [f, LinearMap.codRestrict_apply] at hy
  dsimp
  rw [← HomologicalComplex.Hom.comm_apply]
  simpa using hy

/-- Completeness of the stages below `a` in degree `m` passes to the stages below any `i ≤ a`. -/
private lemma isCompleteFiltration_range_arrow_f_of_le {a i m : ℤ} (hia : i ≤ a)
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f m).hom) :
    TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (i - k)).arrow.f m).hom := by
  convert hc.comp_add_right (a - i).toNat using 2 with k
  exact congrArg (fun j ↦ LinearMap.range ((F j).arrow.f m).hom) (by lia)

/-- **The filtration of the abutment of a complete filtration is separated at `a`.** Under the
hypotheses of `CochainComplex.isZero_homology_of_isCompleteFiltration` in degree `n`, the `a`th
piece `F_a H^n`, the image of `H^n(F_a) ⟶ H^n(K)`, vanishes. -/
theorem isZero_filtrationAbutmentFiltration_of_isCompleteFiltration {a n : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (a - k)).arrow.f (n - 1)).hom)
    (hs : ∀ x : K.X n, (∀ i, x ∈ LinearMap.range ((F i).arrow.f n).hom) → x = 0)
    (h : ∀ i < a,
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        n)) :
    IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration a n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _
    (isZero_spectralObject_H_bot F hF a n (isZero_homology_of_isCompleteFiltration F hF hc hs h))

/-- **Strong convergence for a complete exhaustive filtration.** Let `pq = (p, q)` and
`n = p + q`. Suppose that every element of `K^{n-1}` lies in some `F_i` and that the graded pieces
`F_{i+1}/F_i` have vanishing `H^{n-1}` for all `i ≥ q + r - 1`. Suppose also that the stages
`F_{q-r+2-k}`, `k ≥ 0`, cut out a complete filtration of `K^n`, that the filtration of `K^{n+1}`
is separated, and that the graded pieces have vanishing `H^{n+1}` for all `i < q - r + 2`. Then
the object at `(p, q)` on page `r ≥ 2` is the graded piece `F_{q+1} H^n / F_q H^n` of the
filtration of the abutment `H^n(K)`. -/
noncomputable def filtrationSpectralSequencePageXIsoGradedOfComplete (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × ℤ)
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (pq.2 - r + 2 - k)).arrow.f (pq.1 + pq.2)).hom)
    (hs : ∀ x : K.X (pq.1 + pq.2 + 1),
      (∀ i, x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 + 1)).hom) → x = 0)
    (h₀ : ∀ i < pq.2 - r + 2,
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        (pq.1 + pq.2 + 1)))
    (h₃ : ∀ i, pq.2 + r - 1 ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        (pq.1 + pq.2 - 1))) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  filtrationSpectralSequencePageXIsoGradedOfExhaustive F hF r hr pq hex
    (isZero_homology_of_isCompleteFiltration F hF (by rwa [add_sub_cancel_right]) hs h₀) h₃

/-- **The comparison theorem for complete exhaustive filtrations.** Let `α` be a morphism between
the functors of filtrations `F` of `K` and `G` of `L`, and let `n` be a degree. Suppose that, in
degrees `m = n` and `m = n + 1`, the stages below `a` of both filtrations cut out complete
filtrations of the terms of degree `m - 1`, both filtrations are separated in degree `m`, and the
graded pieces at all indices `i < a` have vanishing `H^m`. Suppose also that in degrees `n - 1`
and `n` both filtrations are exhaustive and their graded pieces at all indices `i ≥ b` have
vanishing cohomology. If the morphism of spectral sequences induced by `α` is an isomorphism on
every object of some page `r ≥ 2`, then `α.app ⊤` induces an isomorphism on `H^n`. -/
theorem isIso_homologyMap_of_isIso_spectralSequence_page_of_complete
    {L : CochainComplex (ModuleCat R) ℤ} (G : ℤ → Subobject L) (hG : Monotone G)
    (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG) (n : ℤ) {a b : ℤ}
    (hFc : ∀ m, n ≤ m → m ≤ n + 1 → TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (a - k)).arrow.f (m - 1)).hom)
    (hGc : ∀ m, n ≤ m → m ≤ n + 1 → TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((G (a - k)).arrow.f (m - 1)).hom)
    (hFs : ∀ m, n ≤ m → m ≤ n + 1 →
      ∀ x : K.X m, (∀ i, x ∈ LinearMap.range ((F i).arrow.f m).hom) → x = 0)
    (hGs : ∀ m, n ≤ m → m ≤ n + 1 →
      ∀ x : L.X m, (∀ i, x ∈ LinearMap.range ((G i).arrow.f m).hom) → x = 0)
    (hFa : ∀ m, n ≤ m → m ≤ n + 1 → ∀ i < a,
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m))
    (hGa : ∀ m, n ≤ m → m ≤ n + 1 → ∀ i < a,
      IsZero ((cokernel (Subobject.ofLE (G i) (G (i + 1)) (hG (Int.le_add_one le_rfl)))).homology
        m))
    (hFex : ∀ m, n - 1 ≤ m → m ≤ n →
      ∀ x : K.X m, ∃ q, x ∈ LinearMap.range ((F q).arrow.f m).hom)
    (hGex : ∀ m, n - 1 ≤ m → m ≤ n →
      ∀ x : L.X m, ∃ q, x ∈ LinearMap.range ((G q).arrow.f m).hom)
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
    (fun m hm₀ hm₁ i hi ↦ isZero_homology_of_isCompleteFiltration F hF
      (isCompleteFiltration_range_arrow_f_of_le F hi (hFc m hm₀ hm₁)) (hFs m hm₀ hm₁)
      fun j hj ↦ hFa m hm₀ hm₁ j (by lia))
    (fun m hm₀ hm₁ i hi ↦ isZero_homology_of_isCompleteFiltration G hG
      (isCompleteFiltration_range_arrow_f_of_le G hi (hGc m hm₀ hm₁)) (hGs m hm₀ hm₁)
      fun j hj ↦ hGa m hm₀ hm₁ j (by lia))
    hFex hGex hFb hGb r hr h

end Increasing

section Decreasing

variable (F : ℤ → Subobject K) (hF : Antitone F)

/-- **The stages of a complete decreasing filtration with vanishing graded cohomology are
acyclic.** Let `F` be a decreasing filtration of a complex of modules `K`. Suppose that the stages
`F^{a+k}`, `k ≥ 0`, form a complete filtration of `K^{m-1}`, that the filtration of `K^m` is
separated, and that the graded pieces `F^j/F^{j+1}` have vanishing `H^m` for all `j ≥ a`. Then
`H^m(F^a) = 0`. -/
theorem isZero_homology_of_antitone_of_isCompleteFiltration {a m : ℤ}
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (a + k)).arrow.f (m - 1)).hom)
    (hs : ∀ x : K.X m, (∀ j, x ∈ LinearMap.range ((F j).arrow.f m).hom) → x = 0)
    (h : ∀ j, a ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology m)) :
    IsZero ((F a : CochainComplex (ModuleCat R) ℤ).homology m) := by
  have hF' : Monotone (F ∘ Neg.neg) := hF.comp fun _ _ h ↦ neg_le_neg h
  simpa using isZero_homology_of_isCompleteFiltration (F ∘ Neg.neg) hF' (a := -a)
    (by
      convert hc using 2 with k
      exact congrArg (fun j ↦ LinearMap.range ((F j).arrow.f (m - 1)).hom) (by lia))
    (fun x hx ↦ hs x fun j ↦
      cast (congrArg (fun i ↦ x ∈ LinearMap.range ((F i).arrow.f m).hom) (neg_neg j)) (hx (-j)))
    (fun i hi ↦ (h (-i - 1) (by lia)).of_iso
      ((HomologicalComplex.homologyFunctor _ _ m).mapIso
        (Subobject.cokernelOfLEIsoOfEq (by rw [Function.comp_apply]; congr 1; lia)
          (by rw [Function.comp_apply]; congr 1; lia) _ _)))

/-- **Strong convergence of the spectral sequence of a complete exhaustive decreasing
filtration.** Let `F` be a decreasing filtration of a complex of modules. Suppose that every
element of `K^{p+q-1}` lies in some `F^j` and that the graded pieces `F^j/F^{j+1}` have vanishing
`H^{p+q-1}` for all `j ≤ p - r`. Suppose also that the stages `F^{p+r+k}`, `k ≥ 0`, form a
complete filtration of `K^{p+q}`, that the filtration of `K^{p+q+1}` is separated, and that the
graded pieces have vanishing `H^{p+q+1}` for all `j ≥ p + r`. Then the object at `(p, q)` on page
`r ≥ 1` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of
`H^{p+q}(K)`. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIsoGradedOfComplete (r : ℤ)
    (hr : 1 ≤ r) (p q : ℤ)
    (hex : ∀ x : K.X (p + q - 1), ∃ j, x ∈ LinearMap.range ((F j).arrow.f (p + q - 1)).hom)
    (hc : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (p + r + k)).arrow.f (p + q)).hom)
    (hs : ∀ x : K.X (p + q + 1),
      (∀ j, x ∈ LinearMap.range ((F j).arrow.f (p + q + 1)).hom) → x = 0)
    (h₀ : ∀ j, p + r ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q + 1)))
    (h₃ : ∀ j, j ≤ p - r →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q - 1))) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (spectralObject (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))) (-p - 1)
        (p + q)) :=
  decreasingFiltrationSpectralSequencePageXIsoGradedOfExhaustive F hF r hr p q hex
    (isZero_homology_of_antitone_of_isCompleteFiltration F hF (by rwa [add_sub_cancel_right]) hs
      h₀) h₃

end Decreasing

end CochainComplex
