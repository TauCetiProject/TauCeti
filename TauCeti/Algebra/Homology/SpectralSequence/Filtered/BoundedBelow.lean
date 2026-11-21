/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
public import TauCeti.Algebra.Homology.SpectralObject.Image
public import TauCeti.CategoryTheory.Thin

/-!
# Convergence for filtrations bounded below

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex of modules `K`. Suppose
that it is *bounded below* in degree `n + 1`, some stage `F_s` vanishing there, and *exhaustive* in
degree `n - 1`, every element lying in some `F_i`, but with no upper bound: the stages need not
reach `K`, and the quotients `K / F_i` need not have vanishing cohomology. Then, for `n = p + q`,
on every page `r ≥ 2` with `q - r + 2 ≤ s` the object at `(p, q)` maps onto the graded piece
`F_{q+1} H^n / F_q H^n` of the filtration of `H^n(K)`
(`CochainComplex.filtrationSpectralSequencePageXToGraded`), compatibly with the canonical maps to
the objects at `(p, q)` on the later pages
(`CategoryTheory.Abelian.SpectralObject.spectralSequencePageXToPageX`). An element vanishes in the
graded piece exactly when it vanishes on some later page
(`CochainComplex.filtrationSpectralSequencePageXToGraded_eq_zero_iff`). So the graded piece is
the direct limit of the objects at `(p, q)` on the pages `r' ≥ r` along these maps, the canonical
maps `E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1) ⟶ E^n(⊥ ≤ q ≤ q + 1 ≤ q + r' - 1)` of the spectral object.
This is an analogue of the `E∞` part of Weibel's Classical Convergence Theorem 5.5.1(2), whose
`E∞` is the direct limit along the spectral sequence's own maps from page `r` to page `r + 1`
(page `r + 1` being the homology of page `r`), in the form needed when the filtration is not
finite. Identifying `spectralSequencePageXToPageX` with those maps is not done here.
Convergence to `H^n(K)` needs in addition hypotheses in degree `n`, which this file does not
assume: if every element of `K^n` lies in some `F_i`, the filtration of `H^n(K)` is exhaustive
(`CochainComplex.exists_mem_range_filtrationAbutmentFiltrationι`), and if some stage vanishes in
degree `n`, it is bounded below (`CochainComplex.isZero_filtrationAbutmentFiltration_of_isZero_X`).
The strong convergence statements of
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive` need instead the vanishing of the
graded cohomology above some stage, which makes the pages stabilize.

The graded piece is the limit object `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` of the spectral object
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`), and the object on page `r` is
`E^n(⊥ ≤ q ≤ q + 1 ≤ q + r - 1)`. Through `fromE`, these embed in `H^n(F_⊤ / F_q)` and
`H^n(F_{q+r-1} / F_q)`. Since `K / F_q` is the directed union of the subcomplexes
`F_j / F_q`, a class of `H^n(F_j / F_q)` vanishing in `H^n(K / F_q)` vanishes in some
`H^n(F_{j'} / F_q)` (`HomologicalComplex.exists_homologyMap_eq_zero_of_injective`). This is proved
for any functor `G : EInt ⥤ CochainComplex (ModuleCat R) ℤ` with monomorphic transition maps
(`CochainComplex.exists_spectralObject_H_map_twoδ₂Toδ₁'_eq_zero`,
`CochainComplex.exists_mapFourδ₄Toδ₃'_eq_zero`,
`CochainComplex.exists_spectralSequencePageXToPageX_eq_zero`), and then specialized to
filtrations.

## Main definitions

* `CochainComplex.filtrationSpectralSequencePageXToGraded`: the epimorphism from the object at
  `(p, q)` on page `r` onto the graded piece `F_{q+1} H^{p+q} / F_q H^{p+q}`.

## Main results

* `CochainComplex.mem_range_filtrationFunctor_map_f_iff`: an element of the piece `G_b` of the
  functor of a filtration comes from `G_a` exactly when its image in `K` lies in `F_a`.
* `CochainComplex.exists_spectralSequencePageXToPageX_eq_zero`: for a functor `G` exhaustive in
  degree `n - 1`, an element of a page vanishing in `E∞` vanishes on some later page.
* `CochainComplex.spectralSequencePageXToPageX_filtrationSpectralSequencePageXToGraded`: the maps
  onto the graded piece are compatible with the maps to the later pages.
* `CochainComplex.filtrationSpectralSequencePageXToGraded_eq_zero_iff`: an analogue of **the
  Classical Convergence Theorem** for filtrations bounded below and exhaustive: the kernel of the
  map onto the graded piece consists of the elements vanishing on some later page under
  `spectralSequencePageXToPageX`.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Definition 5.2.11 and Theorem 5.5.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, §2.2 and Theorem 2.6.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CochainComplex

universe v

variable {R : Type*} [Ring R]

section Functor

variable (G : EInt ⥤ CochainComplex (ModuleCat.{v} R) ℤ)
  [∀ {a b : EInt} (f : a ⟶ b), Mono (G.map f)]

/-- The map `H^n(q ≤ a) ⟶ H^n(q ≤ b)` of the spectral object of `G`, read through
`spectralObjectHIsoCokernel`, is the map in cohomology of `G_a / G_q ⟶ G_b / G_q`. -/
@[elementwise]
private lemma H_map_twoδ₂Toδ₁'_comp_spectralObjectHIsoCokernel_hom {q a b : EInt} (hqa : q ≤ a)
    (hab : a ≤ b) (n : ℤ) :
    ((spectralObject G).H n).map (twoδ₂Toδ₁' q a b hqa hab) ≫
        (spectralObjectHIsoCokernel G (homOfLE (hqa.trans hab)) n).hom =
      (spectralObjectHIsoCokernel G (homOfLE hqa) n).hom ≫ HomologicalComplex.homologyMap
        (cokernel.map _ _ (𝟙 _) (G.map (homOfLE hab))
          (by rw [← G.map_id]; apply G.map_comp_map_eq_map_comp_map)) n := by
  rw [spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom]
  simp [twoδ₂Toδ₁']

/-- The directed union argument on the quotients: if every element of `G_⊤` in degree `n - 1`
comes from some `G_i`, a class of `H^n(G_j / G_q)` vanishing in `H^n(G_⊤ / G_q)` already vanishes
in some `H^n(G_{j'} / G_q)`, `j' ≥ j`. -/
private lemma exists_homologyMap_cokernelMap_eq_zero {q j n : ℤ} (hqj : q ≤ j)
    (hex : ∀ x : (G.obj ⊤).X (n - 1), ∃ (i : ℤ) (y : (G.obj i).X (n - 1)),
      (G.map (homOfLE (le_top : (i : EInt) ≤ ⊤))).f (n - 1) y = x)
    (y : (cokernel (G.map (homOfLE (show (q : EInt) ≤ j by simpa using hqj)))).homology n)
    (hy : HomologicalComplex.homologyMap (cokernel.map _
      (G.map (homOfLE (le_top : (q : EInt) ≤ ⊤))) (𝟙 _)
      (G.map (homOfLE (le_top : (j : EInt) ≤ ⊤)))
      (by rw [← G.map_id]; apply G.map_comp_map_eq_map_comp_map)) n y = 0) :
    ∃ (j' : ℤ) (hjj' : j ≤ j'), HomologicalComplex.homologyMap (cokernel.map _
      (G.map (homOfLE (show (q : EInt) ≤ j' by simp; lia))) (𝟙 _)
      (G.map (homOfLE (show (j : EInt) ≤ j' by simpa using hjj')))
      (by rw [← G.map_id]; apply G.map_comp_map_eq_map_comp_map)) n y = 0 := by
  -- The quotients `G_a / G_q` form a directed family of subcomplexes of `G_⊤ / G_q`.
  let L (a : {a : ℤ // q ≤ a}) : CochainComplex (ModuleCat.{v} R) ℤ :=
    cokernel (G.map (homOfLE (show (q : EInt) ≤ a.val by simpa using a.property)))
  let φ (a : {a : ℤ // q ≤ a}) :
      L a ⟶ cokernel (G.map (homOfLE (le_top : (q : EInt) ≤ ⊤))) :=
    cokernel.map _ _ (𝟙 _) (G.map (homOfLE le_top))
      (by rw [← G.map_id]; apply G.map_comp_map_eq_map_comp_map)
  have hφ (a : {a : ℤ // q ≤ a}) : Mono (φ a) :=
    Abelian.mono_cokernel_map_of_isPullback (IsPullback.of_vert_isIso_mono ⟨by
      rw [← G.map_id]; apply G.map_comp_map_eq_map_comp_map⟩)
  let ψ (a : {a : ℤ // q ≤ a}) (ha : j ≤ a.val) : L ⟨j, hqj⟩ ⟶ L a :=
    cokernel.map _ _ (𝟙 _) (G.map (homOfLE (show (j : EInt) ≤ a.val by simpa using ha)))
      (by rw [← G.map_id]; apply G.map_comp_map_eq_map_comp_map)
  have hψ (a : {a : ℤ // q ≤ a}) (ha : j ≤ a.val) : ψ a ha ≫ φ a = φ ⟨j, hqj⟩ := by
    apply coequalizer.hom_ext
    simp only [ψ, φ, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc, ← G.map_comp_assoc]
    rfl
  -- Every element of `(G_⊤ / G_q)^{n-1}` comes from some `G_a / G_q` with `j ≤ a`.
  have hcover (z : (cokernel (G.map (homOfLE (le_top : (q : EInt) ≤ ⊤)))).X (n - 1)) :
      ∃ a, ∃ _ : j ≤ a.val, ∃ w, (φ a).f (n - 1) w = z := by
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((cokernel.π (G.map (homOfLE (le_top : (q : EInt) ≤ ⊤)))).f (n - 1))).1 inferInstance z
    obtain ⟨i, w, rfl⟩ := hex z
    refine ⟨⟨max j i, by lia⟩, le_max_left j i,
      (cokernel.π (G.map (homOfLE (show (q : EInt) ≤ ((max j i : ℤ) : EInt) by
        simp; lia)))).f (n - 1) ((G.map (homOfLE (show (i : EInt) ≤ ((max j i : ℤ) : EInt) by
        simp))).f (n - 1) w), ?_⟩
    simp only [φ, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, Category.assoc,
      cokernel.π_desc]
    rw [← Category.assoc, ← G.map_comp]
    rfl
  obtain ⟨a, ha, hya⟩ := HomologicalComplex.exists_homologyMap_eq_zero_of_injective n φ
    (fun a ↦ (ModuleCat.mono_iff_injective _).1 inferInstance) (m := n - 1) (by simp)
    (i := ⟨j, hqj⟩) (P := fun a ↦ j ≤ a.val) ψ hψ hcover _ hy
  exact ⟨a.val, ha, hya⟩

/-- **Vanishing in `H^n(q ≤ ⊤)` is detected at a finite stage.** Suppose that every element of
`G_⊤` in degree `n - 1` comes from some `G_i`, `i : ℤ`. Then a class of `H^n(q ≤ j)` (the
cohomology of `G_j / G_q`) whose image in `H^n(q ≤ ⊤)` vanishes already has vanishing image in
`H^n(q ≤ j')` for some integer `j' ≥ j`. -/
theorem exists_spectralObject_H_map_twoδ₂Toδ₁'_eq_zero {q j n : ℤ} (hqj : q ≤ j)
    (hex : ∀ x : (G.obj ⊤).X (n - 1), ∃ (i : ℤ) (y : (G.obj i).X (n - 1)),
      (G.map (homOfLE (le_top : (i : EInt) ≤ ⊤))).f (n - 1) y = x)
    (y : ((spectralObject G).H n).obj (mk₁ (homOfLE (show (q : EInt) ≤ j by simpa using hqj))))
    (hy : ((spectralObject G).H n).map (twoδ₂Toδ₁' (q : EInt) j ⊤ (by simpa using hqj) le_top)
      y = 0) :
    ∃ (j' : ℤ) (hjj' : j ≤ j'), ((spectralObject G).H n).map
      (twoδ₂Toδ₁' (q : EInt) j j' (by simpa using hqj) (by simpa using hjj')) y = 0 := by
  have hqj' : (q : EInt) ≤ j := by simpa using hqj
  -- Read `y` in the cohomology of the quotients `G_a / G_q`.
  obtain ⟨j', hjj', h⟩ := exists_homologyMap_cokernelMap_eq_zero G hqj hex
    ((spectralObjectHIsoCokernel G (homOfLE hqj') n).hom y)
    (by rw [← H_map_twoδ₂Toδ₁'_comp_spectralObjectHIsoCokernel_hom_apply, hy, map_zero])
  refine ⟨j', hjj', (ModuleCat.mono_iff_injective (spectralObjectHIsoCokernel G
    (homOfLE (show (q : EInt) ≤ j' by simp; lia)) n).hom).1 inferInstance ?_⟩
  rw [H_map_twoδ₂Toδ₁'_comp_spectralObjectHIsoCokernel_hom_apply, h, map_zero]

/-- **Vanishing in `E∞` is detected at a finite stage.** Suppose that every element of `G_⊤` in
degree `n - 1` comes from some `G_i`, `i : ℤ`. Then an element of `E^n(⊥ ≤ q ≤ q + 1 ≤ j)` whose
image in `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` vanishes already has vanishing image in
`E^n(⊥ ≤ q ≤ q + 1 ≤ j')` for some integer `j' ≥ j`. -/
theorem exists_mapFourδ₄Toδ₃'_eq_zero {q j n : ℤ} (hj : q + 1 ≤ j)
    (hex : ∀ x : (G.obj ⊤).X (n - 1), ∃ (i : ℤ) (y : (G.obj i).X (n - 1)),
      (G.map (homOfLE (le_top : (i : EInt) ≤ ⊤))).f (n - 1) y = x)
    (x : (spectralObject G).E (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (coe_le_coe_add_one q))
      (homOfLE (show ((q + 1 : ℤ) : EInt) ≤ (j : EInt) by simpa using hj)) (n - 1) n (n + 1))
    (hx : (spectralObject G).mapFourδ₄Toδ₃' ⊥ q ((q + 1 : ℤ) : EInt) j ⊤ bot_le
      (coe_le_coe_add_one q) (by simpa using hj) le_top (n - 1) n (n + 1) (by lia) (by lia) x = 0) :
    ∃ (j' : ℤ) (hjj' : j ≤ j'), (spectralObject G).mapFourδ₄Toδ₃' ⊥ q ((q + 1 : ℤ) : EInt) j j'
      bot_le (coe_le_coe_add_one q) (by simpa using hj) (by simpa using hjj') (n - 1) n (n + 1)
        (by lia) (by lia) x = 0 := by
  -- Through `fromE`, the canonical maps out of `E^n(⊥ ≤ q ≤ q + 1 ≤ j)` are the maps out of
  -- `H^n(q ≤ j)`.
  have hfromE {a : EInt} (hja : (j : EInt) ≤ a) := ConcreteCategory.congr_hom
    ((spectralObject G).mapFourδ₄Toδ₃'_fromE ⊥ q ((q + 1 : ℤ) : EInt) j a bot_le
      (coe_le_coe_add_one q) (by simpa using hj) hja (n - 1) n (n + 1)) x
  simp only [ConcreteCategory.comp_apply] at hfromE
  -- The image of `x` in `H^n(q ≤ j)` vanishes in `H^n(q ≤ ⊤)`, hence in some `H^n(q ≤ j')`.
  obtain ⟨j', hjj', h⟩ := exists_spectralObject_H_map_twoδ₂Toδ₁'_eq_zero G (by lia : q ≤ j) hex _
    (by rw [← hfromE le_top, hx, map_zero])
  refine ⟨j', hjj', (ModuleCat.mono_iff_injective ((spectralObject G).fromE _ _ _
    (homOfLE (show (q : EInt) ≤ j' by simp; lia)) rfl (n - 1) n (n + 1))).1 inferInstance ?_⟩
  rw [hfromE (by simpa using hjj'), h, map_zero]

/-- **Vanishing in `E∞` is detected on a later page.** Let `pq = (p, q)` and `n = p + q`. Suppose
that `H^{n+1}(⊥ ≤ q - r' + 2)` vanishes for all `r' ≥ r`, and that every element of `G_⊤` in
degree `n - 1` comes from some `G_i`, `i : ℤ`. Then an element of the object at `(p, q)` on page
`r` whose image in `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` vanishes already vanishes on some page `r' ≥ r`. -/
theorem exists_spectralSequencePageXToPageX_eq_zero (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n : ℤ)
    (hn : n = pq.1 + pq.2)
    (h₀ : ∀ r', r ≤ r' → IsZero (((spectralObject G).H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r' + 2 : ℤ) : EInt))))))
    (hex : ∀ x : (G.obj ⊤).X (n - 1), ∃ (i : ℤ) (y : (G.obj i).X (n - 1)),
      (G.map (homOfLE (le_top : (i : EInt) ≤ ⊤))).f (n - 1) y = x)
    (x : ((spectralSequence G).page r).X pq)
    (hx : (spectralObject G).spectralSequencePageXToEInfty r hr pq n hn (h₀ r le_rfl) x = 0) :
    ∃ (r' : ℤ) (hrr' : r ≤ r'),
      (spectralObject G).spectralSequencePageXToPageX r r' hr hrr' pq n hn (h₀ r le_rfl)
        (h₀ r' hrr') x = 0 := by
  rw [spectralSequencePageXToEInfty_def, ConcreteCategory.comp_apply] at hx
  obtain ⟨j', hj', h⟩ := exists_mapFourδ₄Toδ₃'_eq_zero G (q := pq.2) (j := pq.2 + r - 1) (n := n)
    (by lia) hex _ hx
  obtain ⟨r', rfl⟩ : ∃ r', j' = pq.2 + r' - 1 := ⟨j' - pq.2 + 1, by ring⟩
  refine ⟨r', by lia, ?_⟩
  rw [spectralSequencePageXToPageX_def, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h,
    map_zero]

end Functor

section Filtration

variable {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : ℤ → Subobject K) (hF : Monotone F)

/-- An element of the piece `G_b` of the functor of a filtration comes from the piece `G_a`,
`a ≤ b`, exactly when its image in `K` lies in the subcomplex `F_a`. -/
lemma mem_range_filtrationFunctor_map_f_iff {a : ℤ} {b : EInt} (hab : (a : EInt) ≤ b) {m : ℤ}
    (y : ((filtrationFunctor F hF).obj b).X m) :
    y ∈ LinearMap.range (((filtrationFunctor F hF).map (homOfLE hab)).f m).hom ↔
      (filtrationFunctorArrow F hF b).f m y ∈ LinearMap.range ((F a).arrow.f m).hom := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF a)).f m z, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f, filtrationFunctor_map_comp_arrow, filtrationFunctorArrow_coe]
  · rintro ⟨u, hu⟩
    refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF a).symm).f m u,
      (ModuleCat.mono_iff_injective ((filtrationFunctorArrow F hF b).f m)).1 inferInstance ?_⟩
    -- Both sides are the image of `u` in `K`, through `F_a ⟶ G_a ⟶ G_b ⟶ K`.
    rw [← hu, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      filtrationFunctor_map_comp_arrow, eqToHom_comp_filtrationFunctorArrow]

/-- An exhaustive filtration gives an exhaustive functor: every element of `K = G_⊤` in degree
`m` comes from some `G_i = F_i`. -/
lemma exists_filtrationFunctor_map_f_eq {m : ℤ}
    (hex : ∀ x : K.X m, ∃ i, x ∈ LinearMap.range ((F i).arrow.f m).hom)
    (x : ((filtrationFunctor F hF).obj ⊤).X m) :
    ∃ (i : ℤ) (y : ((filtrationFunctor F hF).obj i).X m),
      ((filtrationFunctor F hF).map (homOfLE (le_top : (i : EInt) ≤ ⊤))).f m y = x :=
  let ⟨i, hi⟩ := hex ((filtrationFunctorArrow F hF ⊤).f m x)
  ⟨i, (mem_range_filtrationFunctor_map_f_iff F hF le_top x).2 hi⟩

/-- **The page objects map onto the graded pieces of the abutment.** Let `pq = (p, q)` and
`n = p + q`, and suppose that the stage `F_s` vanishes in degree `n + 1`. On every page `r ≥ 2`
with `q - r + 2 ≤ s`, this is the epimorphism from the object at `(p, q)` onto the graded piece
`F_{q+1} H^n / F_q H^n` of the filtration of `H^n(K)`, through `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`. -/
noncomputable def filtrationSpectralSequencePageXToGraded (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    {s : ℤ} (hs : IsZero ((F s : CochainComplex (ModuleCat.{v} R) ℤ).X (pq.1 + pq.2 + 1)))
    (hrs : pq.2 - r + 2 ≤ s) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ⟶
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  (spectralObject _).spectralSequencePageXToEInfty r hr pq _ rfl
      (isZero_spectralObject_H_bot_of_isZero_X F hF hs hrs) ≫
    ((spectralObject _).EInftyIsoCokernel _ _).hom

/-- `filtrationSpectralSequencePageXToGraded` is the map `spectralSequencePageXToEInfty` onto
`E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` followed by its identification with the graded piece. -/
lemma filtrationSpectralSequencePageXToGraded_def (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) {s : ℤ}
    (hs : IsZero ((F s : CochainComplex (ModuleCat.{v} R) ℤ).X (pq.1 + pq.2 + 1)))
    (hrs : pq.2 - r + 2 ≤ s) :
    filtrationSpectralSequencePageXToGraded F hF r hr pq hs hrs =
      (spectralObject _).spectralSequencePageXToEInfty r hr pq _ rfl
          (isZero_spectralObject_H_bot_of_isZero_X F hF hs hrs) ≫
        ((spectralObject _).EInftyIsoCokernel _ _).hom :=
  (rfl)

instance (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) {s : ℤ}
    (hs : IsZero ((F s : CochainComplex (ModuleCat.{v} R) ℤ).X (pq.1 + pq.2 + 1)))
    (hrs : pq.2 - r + 2 ≤ s) :
    Epi (filtrationSpectralSequencePageXToGraded F hF r hr pq hs hrs) := by
  rw [filtrationSpectralSequencePageXToGraded_def]
  infer_instance

/-- The maps onto the graded piece are compatible with the maps from a page to later pages. -/
@[reassoc (attr := simp)]
lemma spectralSequencePageXToPageX_filtrationSpectralSequencePageXToGraded (r r' : ℤ) (hr : 2 ≤ r)
    (hrr' : r ≤ r') (pq : ℤ × ℤ) {s : ℤ}
    (hs : IsZero ((F s : CochainComplex (ModuleCat.{v} R) ℤ).X (pq.1 + pq.2 + 1)))
    (hrs : pq.2 - r + 2 ≤ s) :
    (spectralObject _).spectralSequencePageXToPageX r r' hr hrr' pq _ rfl
        (isZero_spectralObject_H_bot_of_isZero_X F hF hs hrs)
        (isZero_spectralObject_H_bot_of_isZero_X F hF hs (by lia)) ≫
      filtrationSpectralSequencePageXToGraded F hF r' (hr.trans hrr') pq hs (by lia) =
    filtrationSpectralSequencePageXToGraded F hF r hr pq hs hrs := by
  rw [filtrationSpectralSequencePageXToGraded_def, filtrationSpectralSequencePageXToGraded_def,
    spectralSequencePageXToPageX_spectralSequencePageXToEInfty_assoc]

/-- **An analogue of Weibel's Classical Convergence Theorem for filtrations bounded below**, for
the canonical maps `spectralSequencePageXToPageX` between pages. Let `pq = (p, q)` and
`n = p + q`. Suppose that the stage `F_s` vanishes in degree `n + 1` and that every element of
`K^{n-1}` lies in some stage `F_i`; no upper bound on the filtration is assumed. On every page
`r ≥ 2` with `q - r + 2 ≤ s`, an element of the object at `(p, q)` vanishes in the graded piece
`F_{q+1} H^n / F_q H^n` exactly when it vanishes on some later page `r'` under the canonical map
`spectralSequencePageXToPageX`. Together with the surjectivity of
`filtrationSpectralSequencePageXToGraded`, this says that the graded piece is the direct limit of
the objects at `(p, q)` on the pages `r' ≥ r` along these maps. They are not yet identified with
the spectral sequence's own maps from page `r` to page `r + 1`. -/
theorem filtrationSpectralSequencePageXToGraded_eq_zero_iff (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    {s : ℤ} (hs : IsZero ((F s : CochainComplex (ModuleCat.{v} R) ℤ).X (pq.1 + pq.2 + 1)))
    (hrs : pq.2 - r + 2 ≤ s)
    (hex : ∀ x : K.X (pq.1 + pq.2 - 1), ∃ i,
      x ∈ LinearMap.range ((F i).arrow.f (pq.1 + pq.2 - 1)).hom)
    (x : ((spectralSequence (filtrationFunctor F hF)).page r).X pq) :
    filtrationSpectralSequencePageXToGraded F hF r hr pq hs hrs x = 0 ↔
      ∃ (r' : ℤ) (hrr' : r ≤ r'),
        (spectralObject _).spectralSequencePageXToPageX r r' hr hrr' pq _ rfl
          (isZero_spectralObject_H_bot_of_isZero_X F hF hs hrs)
          (isZero_spectralObject_H_bot_of_isZero_X F hF hs (by lia)) x = 0 := by
  rw [filtrationSpectralSequencePageXToGraded_def, ConcreteCategory.comp_apply,
    (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono ((spectralObject _).EInftyIsoCokernel
      _ _).hom) |>.eq_iff' (map_zero _)]
  constructor
  · exact exists_spectralSequencePageXToPageX_eq_zero _ r hr pq _ rfl
      (fun r' hrr' ↦ isZero_spectralObject_H_bot_of_isZero_X F hF hs (by lia))
      (exists_filtrationFunctor_map_f_eq F hF hex) x
  · rintro ⟨r', hrr', h⟩
    rw [← spectralSequencePageXToPageX_spectralSequencePageXToEInfty _ r r' hr hrr' pq _ rfl _
      (isZero_spectralObject_H_bot_of_isZero_X F hF hs (by lia)), ConcreteCategory.comp_apply, h,
      map_zero]

end Filtration

end CochainComplex
