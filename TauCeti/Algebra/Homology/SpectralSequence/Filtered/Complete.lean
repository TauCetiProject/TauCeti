/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.CategoryTheory.Subobject.Cokernel
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

/-!
# Convergence for complete filtrations

Let `F` be an increasing filtration of a cochain complex of modules `K`. The convergence theorems
of `TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive` control the top of the
filtration through exhaustiveness, but at the bottom they need the stages `F_a` themselves to be
acyclic in the relevant degrees, as happens when `F_a = ⊥`. Decreasing filtrations of cochain
complexes are often not of this kind: in the filtration of the singular cochains of a space by
vanishing on the preimages of the skeleta of a CW base, no stage vanishes in any degree unless the
base is finite-dimensional, but the filtration is complete and separated, and its first page
vanishes below the horizontal axis. This file
proves the missing acyclicity, and hence strong convergence, for complete filtrations.

Completeness is Tau Ceti's `TauCeti.IsCompleteFiltration`, imposed degreewise on the descending
chain of submodules `F_{a-k}^n ⊆ K^n`, `k : ℕ`, the ranges of the inclusions of the stages. The
key statement is `CochainComplex.isZero_homology_of_isCompleteFiltration`: for subcomplexes
`G 0 ⊇ G 1 ⊇ ⋯`, complete and separated in degrees `m - 1` and `m`, whose quotients
`G k / G (k + 1)` have vanishing `H^m`, the first term `G 0` has vanishing `H^m`. A cocycle `z` in
`G 0` is pushed down the chain one stage at a time
(`CochainComplex.exists_sub_d_mem_range_of_isZero_homology_cokernel`), `z = d y₀ + ⋯ + d y_{k-1}
+ z_k` with `y_i ∈ G i` and `z_k ∈ G k`; completeness in degree `m - 1` sums the series `∑ yᵢ`,
and separation in degree `m` shows that its coboundary is `z`. This is the elementwise form of
the Mittag-Leffler argument through the Milnor sequence of the tower `G 0 / G k`: the vanishing
of `H^m` on the graded pieces gives surjective transitions on `H^{m-1}` of that tower, hence no
`lim¹` term. Only `H^m` of the graded pieces enters.

For an increasing filtration indexed by `ℤ` this gives the acyclicity of `F_a` from that of the
graded pieces below `a` (`CochainComplex.isZero_homology_of_isCompleteFiltration_of_monotone`),
and dually for decreasing filtrations above `p`
(`CochainComplex.isZero_homology_of_isCompleteFiltration_of_antitone`). Consequently:

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

/-- **Pushing a cocycle down one stage.** Let `S ≤ T` be subcomplexes of `K` such that `T/S` has
vanishing `H^m`. Then every cocycle `z ∈ K^m` lying in `T` differs from a cocycle lying in `S` by
the coboundary `d y` of some `y ∈ T^{m-1}`. -/
lemma exists_sub_d_mem_range_of_isZero_homology_cokernel {S T : Subobject K} (hST : S ≤ T)
    {m' m : ℤ} (hm : m' + 1 = m)
    (h : IsZero ((cokernel (Subobject.ofLE S T hST)).homology m)) {z : K.X m}
    (hz : z ∈ LinearMap.range (T.arrow.f m).hom) (hdz : (K.d m (m + 1)).hom z = 0) :
    ∃ y ∈ LinearMap.range (T.arrow.f m').hom,
      z - (K.d m' m).hom y ∈ LinearMap.range (S.arrow.f m).hom := by
  obtain ⟨z, rfl⟩ := hz
  have hinj (U : Subobject K) (n : ℤ) : Function.Injective (U.arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hdz' : ((T : CochainComplex (ModuleCat R) ℤ).d m (m + 1)).hom z = 0 :=
    hinj T _ (by rw [← HomologicalComplex.Hom.comm_apply, hdz, map_zero])
  -- The image of `z` in `T/S` is a cocycle, homologous to zero since `H^m(T/S) = 0`.
  let S' := ShortComplex.cokernelSequence (Subobject.ofLE S T hST)
  have hdz₃ : (S'.X₃.d m (m + 1)).hom ((S'.g.f m).hom z) = 0 :=
    HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero S'.g m (m + 1) z hdz'
  -- The terms `S'.X₁` and `S'.X₂` are `S` and `T` by definition (`cokernelSequence_X₁`,
  -- `cokernelSequence_X₂`); the type ascriptions below record the elements in these terms.
  obtain ⟨b, a, hab⟩ : ∃ (b : (T : CochainComplex (ModuleCat R) ℤ).X m')
      (a : (S : CochainComplex (ModuleCat R) ℤ).X m),
      z = ((T : CochainComplex (ModuleCat R) ℤ).d m' m).hom b +
        ((Subobject.ofLE S T hST).f m).hom a := by
    obtain ⟨b, a, -, hab⟩ := (TauCeti.cokernelSequence_shortExact
      (Subobject.ofLE S T hST)).moduleCat_exists_sub_eq_d_add m (m + 1) m' (by simp; lia) z 0
      (by exact hdz'.trans (map_zero _).symm)
      (S'.X₃.moduleCatCyclesMk _ (m + 1) (by simp) hdz₃) 0
      (by exact (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm) (by simp)
      ((ModuleCat.isZero_iff_subsingleton.1 h).elim _ _)
    exact ⟨b, a, (sub_zero z).symm.trans hab⟩
  -- So `z = d b + a` with `b ∈ T^{m-1}` and `a ∈ S^m`.
  refine ⟨_, ⟨b, rfl⟩, a, ?_⟩
  rw [HomologicalComplex.Hom.comm_apply, ← map_sub, hab, add_sub_cancel_left,
    ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f]
  exact congr(($(Subobject.ofLE_arrow hST).f m).hom a).symm

/-- **Acyclicity of the first term of a complete chain of subcomplexes.** Let
`G 0 ⊇ G 1 ⊇ G 2 ⊇ ⋯` be subcomplexes of a complex of modules `K` which, degreewise, form a
complete separated filtration in degrees `m - 1` and `m`. If every quotient `G k / G (k + 1)` has
vanishing `H^m`, then so does `G 0`. -/
theorem isZero_homology_of_isCompleteFiltration (G : ℕ → Subobject K) (hG : Antitone G)
    {m' m : ℤ} (hm : m' + 1 = m)
    (hc₀ : TauCeti.IsCompleteFiltration fun k ↦ LinearMap.range ((G k).arrow.f m').hom)
    (hc₁ : TauCeti.IsCompleteFiltration fun k ↦ LinearMap.range ((G k).arrow.f m).hom)
    (h : ∀ k : ℕ,
      IsZero ((cokernel (Subobject.ofLE (G (k + 1)) (G k) (hG k.le_succ))).homology m)) :
    IsZero ((G 0 : CochainComplex (ModuleCat R) ℤ).homology m) := by
  -- Every cocycle of `K` in `G k` is cohomologous, within `G k`, to a cocycle in `G (k + 1)`.
  have step (k : ℕ) (z : K.X m) (hz : z ∈ LinearMap.range ((G k).arrow.f m).hom)
      (hdz : (K.d m (m + 1)).hom z = 0) :
      ∃ y ∈ LinearMap.range ((G k).arrow.f m').hom,
        z - (K.d m' m).hom y ∈ LinearMap.range ((G (k + 1)).arrow.f m).hom :=
    exists_sub_d_mem_range_of_isZero_homology_cokernel (hG k.le_succ) hm (h k) hz hdz
  choose! y hy hyz using step
  -- Iterating, a cocycle `z` in `G 0` gives cocycles `zs k ∈ G k` with
  -- `zs k = z - d (y 0 + ⋯ + y (k - 1))`, and the series `∑ y k` converges.
  have key (z : K.X m) (hz : z ∈ LinearMap.range ((G 0).arrow.f m).hom)
      (hdz : (K.d m (m + 1)).hom z = 0) :
      ∃ s ∈ LinearMap.range ((G 0).arrow.f m').hom, (K.d m' m).hom s = z := by
    let zs : ℕ → K.X m := fun k ↦ Nat.rec z (fun k zk ↦ zk - (K.d m' m).hom (y k zk)) k
    have hzs_succ (k : ℕ) : zs (k + 1) = zs k - (K.d m' m).hom (y k (zs k)) := rfl
    have hzs (k : ℕ) :
        zs k ∈ LinearMap.range ((G k).arrow.f m).hom ∧ (K.d m (m + 1)).hom (zs k) = 0 := by
      induction k with
      | zero => exact ⟨hz, hdz⟩
      | succ k ih =>
        rw [hzs_succ]
        refine ⟨hyz k _ ih.1 ih.2, ?_⟩
        rw [map_sub, ih.2, HomologicalComplex.d_comp_d_apply, sub_zero]
    have hzsum (n : ℕ) : zs n = z - (K.d m' m).hom (∑ k ∈ Finset.range n, y k (zs k)) := by
      induction n with
      | zero => simp [zs]
      | succ n ih =>
        rw [hzs_succ, Finset.sum_range_succ, map_add, ← sub_sub, ← ih]
    obtain ⟨s, hs⟩ := hc₀.exists_limit (fun n ↦ ∑ k ∈ Finset.range n, y k (zs k)) fun n ↦ by
      simpa [Finset.sum_range_succ] using hy n _ (hzs n).1 (hzs n).2
    refine ⟨s, by simpa using hs 0, sub_eq_zero.1 (hc₁.eq_zero_of_forall_mem _ fun n ↦ ?_)⟩
    have hsub : (K.d m' m).hom s - z =
        (K.d m' m).hom (s - ∑ k ∈ Finset.range n, y k (zs k)) - zs n := by
      rw [hzsum n, map_sub]
      abel
    rw [hsub]
    obtain ⟨t, ht⟩ := hs n
    exact sub_mem ⟨_, by rw [← ht, HomologicalComplex.Hom.comm_apply]⟩ (hzs n).1
  -- Transport the statement from `K` to the subcomplex `G 0`.
  have hinj (n : ℤ) : Function.Injective ((G 0).arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((HomologicalComplex.exactAt_iff' _ m' m (m + 1) (by simp; lia) (by simp)).2
      ((ShortComplex.moduleCat_exact_iff _).2 fun x hx ↦ ?_))
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := key _ ⟨x, rfl⟩
    (HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero (G 0).arrow m (m + 1) x hx)
  exact ⟨s, hinj m ((HomologicalComplex.Hom.comm_apply (G 0).arrow m' m s).symm.trans hs)⟩

/-- **Acyclicity of a stage of a complete increasing filtration.** Let `F` be an increasing
filtration of a complex of modules `K` which, degreewise, is complete and separated below `F_a` in
degrees `m - 1` and `m`. If the graded pieces `F_{i+1}/F_i` have vanishing `H^m` for all `i < a`,
then so does `F_a`. -/
theorem isZero_homology_of_isCompleteFiltration_of_monotone (F : ℤ → Subobject K)
    (hF : Monotone F) {a m' m : ℤ} (hm : m' + 1 = m)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f m').hom)
    (hc₁ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f m).hom)
    (h : ∀ i, i < a →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m)) :
    IsZero ((F a : CochainComplex (ModuleCat R) ℤ).homology m) := by
  have := isZero_homology_of_isCompleteFiltration (fun k : ℕ ↦ F (a - k))
    (fun k l hkl ↦ hF (by lia)) hm hc₀ hc₁ fun k ↦
      (h (a - (k + 1 : ℕ)) (by lia)).of_iso ((HomologicalComplex.homologyFunctor _ _ m).mapIso
        (Subobject.cokernelOfLEIsoOfEq rfl (by congr 1; lia) _ _))
  rwa [Nat.cast_zero, sub_zero] at this

/-- **Acyclicity of a stage of a complete decreasing filtration.** Let `F` be a decreasing
filtration of a complex of modules `K` which, degreewise, is complete and separated above `F^p` in
degrees `m - 1` and `m`. If the graded pieces `F^j/F^{j+1}` have vanishing `H^m` for all `j ≥ p`,
then so does `F^p`. -/
theorem isZero_homology_of_isCompleteFiltration_of_antitone (F : ℤ → Subobject K)
    (hF : Antitone F) {p m' m : ℤ} (hm : m' + 1 = m)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (p + k)).arrow.f m').hom)
    (hc₁ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (p + k)).arrow.f m).hom)
    (h : ∀ j, p ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology m)) :
    IsZero ((F p : CochainComplex (ModuleCat R) ℤ).homology m) := by
  have := isZero_homology_of_isCompleteFiltration (fun k : ℕ ↦ F (p + k))
    (fun k l hkl ↦ hF (by lia)) hm hc₀ hc₁ fun k ↦
      (h (p + k) (by lia)).of_iso ((HomologicalComplex.homologyFunctor _ _ m).mapIso
        (Subobject.cokernelOfLEIsoOfEq (by congr 1; lia) rfl _ _))
  rwa [Nat.cast_zero, add_zero] at this

/-- **The filtration of the abutment of a complete filtration is separated.** Under the hypotheses
of `CochainComplex.isZero_homology_of_isCompleteFiltration_of_monotone` in degrees `n - 1` and
`n`, the `a`th piece `F_a H^n` of the filtration of the abutment `H^n(K)` vanishes. -/
lemma isZero_filtrationAbutmentFiltration_of_isCompleteFiltration (F : ℤ → Subobject K)
    (hF : Monotone F) {a n' n : ℤ} (hn : n' + 1 = n)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f n').hom)
    (hc₁ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f n).hom)
    (h : ∀ i, i < a →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        n)) :
    IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration a n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _ (isZero_spectralObject_H_bot F hF a n
    (isZero_homology_of_isCompleteFiltration_of_monotone F hF hn hc₀ hc₁ h))

/-- **Strong convergence for a complete exhaustive filtration.** Let `pq = (p, q)` and
`n = p + q`. Suppose that every element of `K^{n-1}` lies in some `F_i`, that below `F_{q-r+2}`
the filtration is degreewise complete and separated in degrees `n` and `n + 1`, and that the
graded pieces `F_{i+1}/F_i` have vanishing `H^{n+1}` for all `i < q - r + 2` and vanishing
`H^{n-1}` for all `i ≥ q + r - 1`. Then the object at `(p, q)` on page `r ≥ 2` is the graded piece
`F_{q+1} H^n / F_q H^n` of the filtration of the abutment `H^n(K)`. -/
noncomputable def filtrationSpectralSequencePageXIsoGradedOfComplete (F : ℤ → Subobject K)
    (hF : Monotone F) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (pq.2 - r + 2 - k)).arrow.f (pq.1 + pq.2)).hom)
    (hc₁ : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (pq.2 - r + 2 - k)).arrow.f (pq.1 + pq.2 + 1)).hom)
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
    (isZero_homology_of_isCompleteFiltration_of_monotone F hF rfl hc₀ hc₁ h₀) h₃

/-- **The comparison theorem for complete exhaustive filtrations.** Let `α` be a morphism between
the functors of filtrations `F` of `K` and `G` of `L`, and let `n` be a degree. Suppose that both
filtrations are degreewise complete and separated in degrees `n - 1` to `n + 1`, that in degrees
`n - 1` and `n` every element of `K` and of `L` lies in some stage of the filtration, and that the
graded pieces of both filtrations have vanishing cohomology in degrees `n` and `n + 1` at all
indices `i < a`, and in degrees `n - 1` and `n` at all indices `i ≥ b`. If the morphism of
spectral sequences induced by `α` is an isomorphism on every object of some page `r ≥ 2`, then
`α.app ⊤` induces an isomorphism on `H^n`. -/
theorem isIso_homologyMap_of_isIso_spectralSequence_page_of_complete
    {L : CochainComplex (ModuleCat.{v} R) ℤ} (F : ℤ → Subobject K) (hF : Monotone F)
    (G : ℤ → Subobject L) (hG : Monotone G) (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG)
    (n : ℤ) {a b : ℤ}
    (hFc : ∀ m, n - 1 ≤ m → m ≤ n + 1 → ∀ i, TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (i - k)).arrow.f m).hom)
    (hGc : ∀ m, n - 1 ≤ m → m ≤ n + 1 → ∀ i, TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((G (i - k)).arrow.f m).hom)
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
      (sub_add_cancel m 1) (hFc _ (by lia) (by lia) i) (hFc m (by lia) hm₁ i)
      fun j hj ↦ hFa m hm₀ hm₁ j (by lia))
    (fun m hm₀ hm₁ i hi ↦ isZero_homology_of_isCompleteFiltration_of_monotone G hG
      (sub_add_cancel m 1) (hGc _ (by lia) (by lia) i) (hGc m (by lia) hm₁ i)
      fun j hj ↦ hGa m hm₀ hm₁ j (by lia))
    hFex hGex hFb hGb r hr h

/-- **Strong convergence of the spectral sequence of a complete decreasing filtration.** Let `F` be
a decreasing filtration of a complex of modules. Suppose that every element of `K^{p+q-1}` lies in
some `F^j`, that above `F^{p+r}` the filtration is degreewise complete and separated in degrees
`p + q` and `p + q + 1`, and that the graded pieces `F^j/F^{j+1}` have vanishing `H^{p+q+1}` for
all `j ≥ p + r` and vanishing `H^{p+q-1}` for all `j ≤ p - r`. Then the object at `(p, q)` on page
`r ≥ 1` is the graded piece `F^p H^{p+q} / F^{p+1} H^{p+q}` of the induced filtration of
`H^{p+q}(K)`. -/
noncomputable def decreasingFiltrationSpectralSequencePageXIsoGradedOfComplete
    (F : ℤ → Subobject K) (hF : Antitone F) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hex : ∀ x : K.X (p + q - 1), ∃ j, x ∈ LinearMap.range ((F j).arrow.f (p + q - 1)).hom)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (p + r + k)).arrow.f (p + q)).hom)
    (hc₁ : TauCeti.IsCompleteFiltration fun k : ℕ ↦
      LinearMap.range ((F (p + r + k)).arrow.f (p + q + 1)).hom)
    (h₀ : ∀ j, p + r ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q + 1)))
    (h₃ : ∀ j, j ≤ p - r →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology (p + q - 1))) :
    ((decreasingFiltrationSpectralSequence F hF).page r).X (p, q) ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (spectralObject (filtrationFunctor _ (hF.comp fun _ _ h ↦ neg_le_neg h))) (-p - 1)
        (p + q)) :=
  decreasingFiltrationSpectralSequencePageXIsoGradedOfExhaustive F hF r hr p q hex
    (isZero_homology_of_isCompleteFiltration_of_antitone F hF rfl hc₀ hc₁ h₀) h₃

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
    (hc _ _) (hc _ _) (fun j hj ↦ hq j _ (by lia)) fun j hj ↦ by
      -- Below the filtration index `0` the graded pieces are `K/K = 0`.
      refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ _).mapIso
        (Subobject.cokernelOfLEIsoOfEq (hF_top (j + 1) (by lia)) (hF_top j (by lia)) _ le_rfl))
      have : IsIso (Subobject.ofLE (⊤ : Subobject K) ⊤ le_rfl) := by
        rw [Subobject.ofLE_refl]
        infer_instance
      exact (HomologicalComplex.acyclic_of_isZero _ (isZero_cokernel_of_epi _) _).isZero_homology

end CochainComplex
