/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Convergence for exhaustive filtrations

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex of modules `K`. The
filtration is *exhaustive* in degree `n` if every element of `K^n` lies in some `F_q`. Such a
filtration need not reach `K` at any finite stage: the skeletal filtration of the singular chains
of a fibration over an infinite CW complex, or the cell filtration of a twisted complex with
infinitely many generators, are exhaustive but not finite. This file proves two convergence
statements for the spectral sequence of an exhaustive filtration.

* The filtration of the abutment `H^n(K)` is exhaustive: every class lies in some piece `F_q H^n`
  (`CochainComplex.exists_mem_range_filtrationAbutmentFiltrationι`). Here `F_q H^n` is the image
  of `H^n(F_q) ⟶ H^n(K)`
  (`CochainComplex.toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom`), and its graded
  pieces are the limit objects `E∞` (`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`).
  When moreover `F_a = ⊥`, the filtration of `H^n(K)` vanishes at `a`
  (`CochainComplex.isZero_filtrationAbutmentFiltration`).
* If the graded pieces `F_{i+1}/F_i` have vanishing `H^m` for all `i ≥ b`, so does the quotient
  `K/F_b` (`CochainComplex.isZero_homology_cokernel_arrow_of_exhaustive`). For a first-quadrant
  spectral sequence this holds in every degree, for some `b` depending on the degree. Then
  `F_b H^n = H^n(K)` (`CochainComplex.isIso_filtrationAbutmentFiltrationι_of_exhaustive`). If
  moreover `H^{n+1}(F_{q-r+2})` vanishes (for instance if `F_{q-r+2} = ⊥`), the object at `(p, q)`
  with `p + q = n` on page `r` is the corresponding graded piece of `H^n(K)`
  (`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfExhaustive`). If the cohomology of
  the stages `F_i` and `G_i` of two filtrations vanishes in degrees `n` and `n + 1` for all `i ≤ a`
  (for instance if `F_a = G_a = ⊥`), a morphism of such filtered complexes which is an isomorphism
  on some page induces an isomorphism on `H^n`
  (`CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page_of_exhaustive`).

The vanishing of `H^m(F_j/F_b)` for every finite stage `j ≥ b` holds in any abelian category
(`CochainComplex.isZero_homology_cokernel_ofLE_of_isZero`). The passage to `K/F_b`, the directed
union of the subcomplexes `F_j/F_b`, uses that cohomology classes of a directed union of
subcomplexes of modules come from its members
(`HomologicalComplex.exists_homologyMap_eq_of_injective`).

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, Theorem 2.6.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CochainComplex

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- If the graded pieces `F_{i+1}/F_i` of a filtration have vanishing `H^m` for all `i ≥ b`, then
so do the quotients `F_j/F_b` for all `j ≥ b`. -/
lemma isZero_homology_cokernel_ofLE_of_isZero {b m : ℤ}
    (h : ∀ i, b ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m))
    (j : ℤ) (hj : b ≤ j) :
    IsZero ((cokernel (Subobject.ofLE (F b) (F j) (hF hj))).homology m) := by
  induction j using Int.inductionOn' (b := b) with
  | zero =>
    have : IsIso (Subobject.ofLE (F b) (F b) (hF hj)) := by
      rw [Subobject.ofLE_refl]
      infer_instance
    exact (HomologicalComplex.acyclic_of_isZero _ (isZero_cokernel_of_epi _) m).isZero_homology
  | succ i hi ih =>
    -- The short exact sequence `F_i/F_b ⟶ F_{i+1}/F_b ⟶ F_{i+1}/F_i`.
    have hS := TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact
      (Subobject.ofLE (F b) (F i) (hF hi)) (Subobject.ofLE (F i) (F (i + 1))
        (hF (Int.le_add_one le_rfl)))
    refine IsZero.of_iso ?_ (HomologicalComplex.homologyMapIso
      (cokernelIsoOfEq (Subobject.ofLE_comp_ofLE (F b) (F i) (F (i + 1)) (hF hi)
        (hF (Int.le_add_one le_rfl)))) m).symm
    exact (hS.homology_exact₂ m).isZero_X₂ ((ih hi).eq_of_src _ _) ((h i hi).eq_of_tgt _ _)
  | pred i hi => lia

end Abelian

section ModuleCat

universe v

variable {R : Type*} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- **The filtration of the abutment of an exhaustive filtration is exhaustive.** If every element
of `K^n` lies in some `F_q`, then every element of the abutment `H^n(K)` lies in some piece
`F_q H^n` of its filtration. -/
theorem exists_mem_range_filtrationAbutmentFiltrationι {n : ℤ}
    (hex : ∀ x : K.X n, ∃ q, x ∈ LinearMap.range ((F q).arrow.f n).hom)
    (x : (spectralObject (filtrationFunctor F hF)).abutment n) :
    ∃ q, x ∈ LinearMap.range
      ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationι q n).hom := by
  -- The class of `x` in `H^n(K)` comes from some `H^n(F_q)`.
  obtain ⟨q, y, hy⟩ := HomologicalComplex.exists_homologyMap_eq_of_injective n
    (fun q ↦ (F q).arrow) (fun _ ↦ (ModuleCat.mono_iff_injective _).1 inferInstance)
    (fun x ↦ (hex x).imp fun _ ⟨y, hy⟩ ↦ ⟨y, hy⟩) ((filtrationAbutmentIso F hF n).hom x)
  refine ⟨q, toFiltrationAbutmentFiltration F hF q n y, ?_⟩
  apply (ModuleCat.mono_iff_injective (filtrationAbutmentIso F hF n).hom).1 inferInstance
  rw [← hy, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom]

/-- **The quotient by a stage of an exhaustive filtration.** If every element of `K^m` lies in
some `F_q` and the quotients `F_j/F_b` have vanishing `H^m` for all `j ≥ b`, then so does `K/F_b`.
-/
lemma isZero_homology_cokernel_arrow_of_isZero_cokernel_ofLE {b m : ℤ}
    (hex : ∀ x : K.X m, ∃ q, x ∈ LinearMap.range ((F q).arrow.f m).hom)
    (h : ∀ j (hj : b ≤ j), IsZero ((cokernel (Subobject.ofLE (F b) (F j) (hF hj))).homology m)) :
    IsZero ((cokernel (F b).arrow).homology m) := by
  -- The quotients `F_j/F_b` form a directed family of subcomplexes of `K/F_b`.
  let φ (j : {j // b ≤ j}) :
      cokernel (Subobject.ofLE (F b) (F j) (hF j.2)) ⟶ cokernel (F b).arrow :=
    cokernel.map _ _ (𝟙 _) (F j).arrow (by simp)
  have hφ (j : {j // b ≤ j}) : Mono (φ j) :=
    Abelian.mono_cokernel_map_of_isPullback (IsPullback.of_vert_isIso_mono ⟨by simp⟩)
  -- Every element of `(K/F_b)^m` comes from some `F_j/F_b`: lift it to `K^m`, and find a stage
  -- `F_q` containing the lift.
  have hcover (x : (cokernel (F b).arrow).X m) : ∃ j y, (φ j).f m y = x := by
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((cokernel.π (F b).arrow).f m)).1
      inferInstance x
    obtain ⟨q, y, rfl⟩ := hex x
    have hq : F q ≤ F (max b q) := hF (le_max_right b q)
    refine ⟨⟨max b q, le_max_left b q⟩,
      (cokernel.π (Subobject.ofLE (F b) (F (max b q)) (hF (le_max_left b q)))).f m
        ((Subobject.ofLE (F q) (F (max b q)) hq).f m y), ?_⟩
    simp [φ, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  -- Hence every class of `H^m(K/F_b)` comes from some `H^m(F_j/F_b) = 0`.
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun z z' ↦ ?_⟩
  suffices ∀ z : (cokernel (F b).arrow).homology m, z = 0 by rw [this z, this z']
  intro z
  obtain ⟨j, y, rfl⟩ := HomologicalComplex.exists_homologyMap_eq_of_injective m φ
    (fun j ↦ (ModuleCat.mono_iff_injective _).1 inferInstance) hcover z
  rw [(ModuleCat.isZero_iff_subsingleton.1 (h j j.2)).elim y 0, map_zero]

/-- **The quotient by a stage of an exhaustive filtration.** If every element of `K^m` lies in
some `F_q` and the graded pieces `F_{i+1}/F_i` have vanishing `H^m` for all `i ≥ b`, then so does
`K/F_b`. -/
theorem isZero_homology_cokernel_arrow_of_exhaustive {b m : ℤ}
    (hex : ∀ x : K.X m, ∃ q, x ∈ LinearMap.range ((F q).arrow.f m).hom)
    (h : ∀ i, b ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m)) :
    IsZero ((cokernel (F b).arrow).homology m) :=
  isZero_homology_cokernel_arrow_of_isZero_cokernel_ofLE F hF hex
    (isZero_homology_cokernel_ofLE_of_isZero F hF h)

/-- **The filtration of the abutment reaches `H^n(K)`.** If every element of `K^n` lies in some
`F_q` and the graded pieces `F_{i+1}/F_i` have vanishing `H^n` for all `i ≥ b`, then the `b`th
piece of the filtration of `H^n(K)` is everything. -/
lemma isIso_filtrationAbutmentFiltrationι_of_exhaustive {b n : ℤ}
    (hex : ∀ x : K.X n, ∃ q, x ∈ LinearMap.range ((F q).arrow.f n).hom)
    (h : ∀ i, b ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        n)) :
    IsIso ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationι b n) :=
  isIso_abutmentFiltrationι _ (isZero_spectralObject_H_top F hF b n
    (isZero_homology_cokernel_arrow_of_exhaustive F hF hex h))

/-- **Strong convergence for an exhaustive filtration.** Let `pq = (p, q)` and `n = p + q`.
Suppose that every element of `K^{n-1}` lies in some `F_i`, that `H^{n+1}(F_{q-r+2})` vanishes,
and that the graded pieces `F_{i+1}/F_i` have vanishing `H^{n-1}` for all `i ≥ q + r - 1`. Then
the object at `(p, q)` on page `r ≥ 2` is the graded piece `F_{q+1} H^n / F_q H^n` of the
filtration of the abutment `H^n(K)`. -/
noncomputable def filtrationSpectralSequencePageXIsoGradedOfExhaustive (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × ℤ)
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (h₀ : IsZero ((F (pq.2 - r + 2) : CochainComplex (ModuleCat R) ℤ).homology (pq.1 + pq.2 + 1)))
    (h₃ : ∀ i, pq.2 + r - 1 ≤ i →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        (pq.1 + pq.2 - 1))) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  filtrationSpectralSequencePageXIsoEInfty F hF r hr pq _ rfl h₀
      (isZero_homology_cokernel_arrow_of_exhaustive F hF hex h₃) ≪≫
    (spectralObject _).EInftyIsoCokernel _ _

/-- **The comparison theorem for exhaustive filtrations.** Let `α` be a morphism between the
functors of filtrations `F` of `K` and `G` of `L`, and let `n` be a degree. Suppose that the
stages `F_i` and `G_i` at all indices `i ≤ a` have vanishing cohomology in degrees `n` and `n + 1`
(for instance `F_a = G_a = ⊥`), that in degrees `n - 1` and `n` every element of `K` and of `L`
lies in some stage of the filtration, and that the graded pieces of both filtrations at all
indices `i ≥ b` have vanishing cohomology (no inequality between `a` and `b` is needed). If the
morphism of spectral sequences induced by `α` is an isomorphism on every object of some page
`r ≥ 2`, then `α.app ⊤` induces an isomorphism on `H^n`. -/
theorem isIso_homologyMap_of_isIso_spectralSequence_page_of_exhaustive
    {L : CochainComplex (ModuleCat R) ℤ} (G : ℤ → Subobject L) (hG : Monotone G)
    (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG) (n : ℤ) {a b : ℤ}
    (hFa : ∀ m, n ≤ m → m ≤ n + 1 → ∀ i, i ≤ a →
      IsZero ((F i : CochainComplex (ModuleCat R) ℤ).homology m))
    (hGa : ∀ m, n ≤ m → m ≤ n + 1 → ∀ i, i ≤ a →
      IsZero ((G i : CochainComplex (ModuleCat R) ℤ).homology m))
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
  isIso_homologyMap_app_top_of_isIso_abutment α n <|
    isIso_hom_app_abutment_of_isIso_page (spectralObjectMap α) n
    (fun m i hm₀ hm₁ hi => isZero_spectralObject_H_bot F hF i m
      (hFa m hm₀ hm₁ i hi))
    (fun m i hm₀ hm₁ hi => isZero_spectralObject_H_bot G hG i m
      (hGa m hm₀ hm₁ i hi))
    (fun m i hm₀ hm₁ hi => isZero_spectralObject_H_top F hF i m
      (isZero_homology_cokernel_arrow_of_exhaustive F hF (hFex m hm₀ hm₁)
        fun j hj ↦ hFb m hm₀ hm₁ j (hi.trans hj)))
    (fun m i hm₀ hm₁ hi => isZero_spectralObject_H_top G hG i m
      (isZero_homology_cokernel_arrow_of_exhaustive G hG (hGex m hm₀ hm₁)
        fun j hj ↦ hGb m hm₀ hm₁ j (hi.trans hj))) r hr h

end ModuleCat

end CochainComplex
