/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.DirectLimit
public import TauCeti.RingTheory.Huber.Continuous.OfCofinal
public import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The adic spectrum of a directed colimit of Huber pairs

Let `(Aᵢ, Aᵢ⁺)` be a directed system of topological rings with plus rings, with continuous
transition maps `tᵢⱼ` carrying `Aᵢ⁺` into `Aⱼ⁺`, and let `φᵢ : Aᵢ → L` be continuous ring
homomorphisms into a topological ring `L` with a plus ring `L⁺`, exhibiting `L` as the colimit
of the rings `Aᵢ` and `L⁺` as the union of the images of the `Aᵢ⁺`. Assume that `L` has a pair
of definition `(L₀, I)` whose ideal of definition `I` consists of images of topologically
nilpotent elements of the stages. For a filtered colimit of Tate pairs with compatible rings of
definition `A_{i,0}` containing a common pseudouniformiser `ϖ`, topologised so that
`L₀ = colim A_{i,0}` is open with its `ϖ`-adic topology, this holds with `I = ϖ L₀`: an element
`ϖ c` with `c` coming from `A_{j,0}` is the image of a topologically nilpotent element of `Aⱼ`.

Then a point of `Spv L` lies in `Spa(L, L⁺)` exactly when all its pullbacks lie in the
`Spa(Aᵢ, Aᵢ⁺)` (`TauCeti.ValuationSpectrum.mem_spa_iff_forall_comap_mem_spa`). The key step is
that continuity of a valuation on `L` can be tested on the stages
(`TauCeti.ValuationSpectrum.isContinuous_of_forall_isContinuous_comap`): by Huber's criterion it
suffices that `v ≤ 1` on `I` and that `v` has cofinal values on a finite generating set of `I`,
and both are read off from continuity at a stage where the relevant elements live. Combined with
the description of `Spv L` as the inverse limit of the `Spv Aᵢ`
(`TauCeti.ValuationSpectrum.directLimitHomeomorph`), this identifies `Spa(L, L⁺)` with the
inverse limit of the adic spectra:

```text
Spa(L, L⁺) ≃ₜ lim_i Spa(Aᵢ, Aᵢ⁺),
```

the limit being realised as the subspace of compatible families in `∏ᵢ Spa(Aᵢ, Aᵢ⁺)`
(`TauCeti.ValuationSpectrum.spaDirectLimitHomeomorph`). Moreover every rational subset
`R(T/s)` of `Spa(L, L⁺)` is the preimage of a rational subset of a single stage, whose
numerators generate the unit ideal when `T` does
(`TauCeti.ValuationSpectrum.exists_spaComap_preimage_rationalSubset`).

## Main results

* `TauCeti.ValuationSpectrum.isContinuous_of_forall_isContinuous_comap`: continuity of a point of
  `Spv L` descends from the stages.
* `TauCeti.ValuationSpectrum.mem_spa_iff_forall_comap_mem_spa`: membership in `Spa(L, L⁺)` is
  tested on the stages.
* `TauCeti.ValuationSpectrum.isEmbedding_pi_spaComap`,
  `TauCeti.ValuationSpectrum.range_pi_spaComap`,
  `TauCeti.ValuationSpectrum.spaDirectLimitHomeomorph`: `Spa(L, L⁺)` is homeomorphic to the
  inverse limit of the `Spa(Aᵢ, Aᵢ⁺)`.
* `TauCeti.ValuationSpectrum.exists_spaComap_preimage_rationalSubset`: rational subsets of
  `Spa(L, L⁺)` come from a finite stage.

## References

* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.6, Remark 2.6.3.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.2, Remark 7.11(1) and Theorem 7.10.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §6, proof of Lemma 6.13(ii).
-/

public section

namespace TauCeti.ValuationSpectrum

open Topology Valuation

variable {ι : Type*} [Preorder ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  [∀ i, TopologicalSpace (A i)] {t : ∀ i j, i ≤ j → A i →+* A j}
  {L : Type*} [CommRing L] [TopologicalSpace L] {φ : ∀ i, A i →+* L}

section Continuity

variable [IsDirectedOrder ι] (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)
  (hcover : ∀ x : L, ∃ i a, φ i a = x)

include hφt hcover in
/-- **Continuity of a valuation on a colimit descends from the stages.** Let `L` be the colimit
of a directed system of topological rings `Aᵢ` with continuous transition maps, and let
`(L₀, I)` be a pair of definition of `L` whose ideal of definition consists of images of
topologically nilpotent elements of the stages. A point of `Spv L` whose pullbacks to all the
`Aᵢ` are continuous is continuous. -/
theorem isContinuous_of_forall_isContinuous_comap [∀ i, ContinuousConstSMul (A i)ᵐᵒᵖ (A i)]
    [SeparatelyContinuousAdd L] (ht : ∀ i j (h : i ≤ j), Continuous (t i j h))
    (P : Huber.PairOfDefinition L)
    (hP : ∀ a ∈ P.idealOfDefinition, ∃ i, ∃ y : A i, IsTopologicallyNilpotent y ∧ φ i y = a)
    {v : Spv L} (hv : ∀ i, (comap (φ i) v).IsContinuous) : v.IsContinuous := by
  classical
  have hw : ∀ i, (v.valuation.comap (φ i)).IsContinuous := fun i ↦ by
    simpa only [← ofValuation_valuation v, comap_ofValuation, isContinuous_ofValuation_iff]
      using hv i
  -- By Huber's criterion it suffices that `v ≤ 1` on `I` and that `v` has cofinal values on a
  -- finite generating set of `I`. An element of `I` is the image of a topologically nilpotent
  -- `y ∈ Aᵢ`, at which the continuous pullback is `< 1`. For cofinality, a positive element of
  -- the value group of `v` is a ratio `v(r)/v(u)`; at a stage where `y`, `r` and `u` all live,
  -- the continuous pullback makes `{x | v(x) < v(r)/v(u)}` open, so it contains a power of the
  -- image of `y`.
  obtain ⟨s, hs⟩ := P.fg_idealOfDefinition
  refine (isContinuous_def v).mpr (P.isContinuous_of_forall_cofinalValue v.valuation hs
    (fun a ha ↦ ?_) fun x hx ↦ ?_)
  · obtain ⟨i, y, hy, hya⟩ := hP a ha
    rw [← hya]
    exact ((hw i).lt_one_of_isTopologicallyNilpotent hy).le
  · obtain ⟨i, y, hy, hyx⟩ := hP x (hs ▸ Ideal.subset_span hx)
    rw [cofinalValue_iff]
    intro γ hγ
    obtain ⟨r, u, hr, hu, hru⟩ := v.valuation.exists_div_eq_of_unit (Units.mk0 γ hγ.ne')
    simp only [Units.val_mk0] at hru
    -- move `y`, a lift of `r` and a lift of `u` to a common stage `m`
    obtain ⟨j, g, hg⟩ := exists_lift hφt hcover {r, u}
    obtain ⟨r', u', rfl, rfl⟩ : ∃ r' u' : A j, φ j r' = r ∧ φ j u' = u :=
      ⟨g r, g u, hg r (by simp), hg u (by simp)⟩
    obtain ⟨m, him, hjm⟩ := directed_of (· ≤ ·) i j
    have hu' : v.valuation.comap (φ m) (t j m hjm u') ≠ 0 := by
      simpa only [comap_apply, hφt] using hu.ne'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent
      (((hw m).isOpen_lt_div (t j m hjm r') hu').mem_nhds
        (by simpa using zero_lt_iff.mpr (div_ne_zero
          (by simpa only [comap_apply, hφt] using hr.ne') hu')))
      (hy.map (ht i m him))
    refine ⟨n, ?_⟩
    have hemb : MonoidWithZeroHom.ValueGroup₀.embedding γ =
        v.valuation (φ j r') / v.valuation (φ j u') := by
      rw [← hru, map_div₀, embedding_restrict, embedding_restrict]
    rw [← map_pow, restrict_lt_iff_lt_embedding, hemb, map_pow, ← hyx]
    simpa only [comap_apply, hφt] using hn

include hφt in
/-- **The ideal of definition of a colimit of Tate rings consists of images of topologically
nilpotent elements.** Let `Qᵢ ⊆ Aᵢ` be subrings of power-bounded elements preserved by the
transition maps (for instance compatible rings of definition `A_{i,0}`), and let `(L₀, I)` be a
pair of definition of `L` with `L₀` contained in the union of the images of the `Qᵢ` and
`I = ϖ L₀` for the image of a topologically nilpotent `ϖ ∈ A_{i₀}`. Then every element of `I` is
the image of a topologically nilpotent element of some stage. This is the hypothesis of
`isContinuous_of_forall_isContinuous_comap` for a filtered colimit of Tate pairs. -/
theorem exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition
    (ht : ∀ i j (h : i ≤ j), Continuous (t i j h)) (Q : ∀ i, Subring (A i))
    (hQ : ∀ i, ∀ c ∈ Q i, Huber.IsPowerBounded c)
    (htQ : ∀ i j (h : i ≤ j), ∀ c ∈ Q i, t i j h c ∈ Q j)
    (P : Huber.PairOfDefinition L) (hP : ∀ c ∈ P.ringOfDefinition, ∃ i, ∃ c' ∈ Q i, φ i c' = c)
    {i₀ : ι} {ϖ : A i₀} (hϖ : IsTopologicallyNilpotent ϖ) {ϖ' : P.ringOfDefinition}
    (hϖ' : (ϖ' : L) = φ i₀ ϖ) (hI : P.idealOfDefinition = Ideal.span {ϖ'})
    {a : P.ringOfDefinition} (ha : a ∈ P.idealOfDefinition) :
    ∃ i, ∃ y : A i, IsTopologicallyNilpotent y ∧ φ i y = a := by
  rw [hI, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  -- `c ϖ` with `c` the image of `c' ∈ Qⱼ` is the image of the product of the power-bounded `c'`
  -- and the topologically nilpotent `ϖ` at a stage above `i₀` and `j`
  obtain ⟨j, c', hc', hc'c⟩ := hP c c.2
  obtain ⟨k, hjk, hi₀k⟩ := directed_of (· ≤ ·) j i₀
  refine ⟨k, t j k hjk c' * t i₀ k hi₀k ϖ,
    (hQ k _ (htQ j k hjk c' hc')).isTopologicallyNilpotent_mul (hϖ.map (ht i₀ k hi₀k)), ?_⟩
  rw [map_mul, hφt, hφt, hc'c, ← hϖ', Subring.coe_mul]

end Continuity

section Spa

variable (Aplus : ∀ i, Subring (A i)) (Lplus : Subring L)
  (hφc : ∀ i, Continuous (φ i)) (hφplus : ∀ i, ∀ a ∈ Aplus i, φ i a ∈ Lplus)

include hφc hφplus in
/-- **Membership in the adic spectrum of a colimit is tested on the stages.** Under the
hypotheses of `isContinuous_of_forall_isContinuous_comap`, if moreover `L⁺` is the union of the
images of the `Aᵢ⁺`, a point of `Spv L` lies in `Spa(L, L⁺)` exactly when its pullback along
every `φᵢ` lies in `Spa(Aᵢ, Aᵢ⁺)`. -/
theorem mem_spa_iff_forall_comap_mem_spa [IsDirectedOrder ι]
    [∀ i, ContinuousConstSMul (A i)ᵐᵒᵖ (A i)] [SeparatelyContinuousAdd L]
    (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)
    (hcover : ∀ x : L, ∃ i a, φ i a = x) (ht : ∀ i j (h : i ≤ j), Continuous (t i j h))
    (P : Huber.PairOfDefinition L)
    (hP : ∀ a ∈ P.idealOfDefinition, ∃ i, ∃ y : A i, IsTopologicallyNilpotent y ∧ φ i y = a)
    (hLplus : ∀ x ∈ Lplus, ∃ i, ∃ a ∈ Aplus i, φ i a = x) (v : Spv L) :
    v ∈ spa Lplus ↔ ∀ i, comap (φ i) v ∈ spa (Aplus i) := by
  refine ⟨fun hv i ↦ comap_mem_spa (hφc i) (hφplus i) hv, fun hv ↦ ?_⟩
  refine (mem_spa_iff Lplus v).mpr ⟨isContinuous_of_forall_isContinuous_comap hφt hcover ht P hP
    fun i ↦ ((mem_spa_iff _ _).mp (hv i)).1, fun x hx ↦ ?_⟩
  obtain ⟨i, a, ha, rfl⟩ := hLplus x hx
  simpa only [comap_vle, map_one] using ((mem_spa_iff _ _).mp (hv i)).2 a ha

variable [IsDirectedOrder ι] (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)
  (hcover : ∀ x : L, ∃ i a, φ i a = x)

include hφt hcover in
/-- **The adic spectrum of a colimit embeds into the product of the adic spectra of the stages.**
If every element of `L` comes from some stage, the map
`Spa(L, L⁺) → ∏ᵢ Spa(Aᵢ, Aᵢ⁺)` given by the pullbacks along the `φᵢ` is a topological embedding.
-/
theorem isEmbedding_pi_spaComap :
    IsEmbedding fun (v : spa Lplus) i ↦ spaComap (φ i) (hφc i) (Aplus i) Lplus (hφplus i) v := by
  refine (IsEmbedding.of_comp_iff (IsEmbedding.piMap fun i ↦ IsEmbedding.subtypeVal)).mp ?_
  have hcomp : (Pi.map fun i ↦ Subtype.val) ∘
      (fun (v : spa Lplus) i ↦ spaComap (φ i) (hφc i) (Aplus i) Lplus (hφplus i) v) =
        (fun (v : Spv L) i ↦ comap (φ i) v) ∘ Subtype.val :=
    funext fun v ↦ funext fun i ↦ spaComap_val _ _ _ _ _ v
  rw [hcomp]
  exact (isEmbedding_pi_comap hφt hcover).comp IsEmbedding.subtypeVal

variable [∀ i, ContinuousConstSMul (A i)ᵐᵒᵖ (A i)] [SeparatelyContinuousAdd L]
  (ht : ∀ i j (h : i ≤ j), Continuous (t i j h))
  (htplus : ∀ i j (h : i ≤ j), ∀ a ∈ Aplus i, t i j h a ∈ Aplus j)
  [DirectedSystem A fun i j h ↦ t i j h]
  (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)
  (P : Huber.PairOfDefinition L)
  (hP : ∀ a ∈ P.idealOfDefinition, ∃ i, ∃ y : A i, IsTopologicallyNilpotent y ∧ φ i y = a)
  (hLplus : ∀ x ∈ Lplus, ∃ i, ∃ a ∈ Aplus i, φ i a = x)

include hφt hcover ht hker hP hLplus in
/-- **The compatible families of points of the adic spectra are the points of the colimit.**
Under the hypotheses of `mem_spa_iff_forall_comap_mem_spa`, and if `L` is the colimit of the
directed system of rings `(Aᵢ, tᵢⱼ)`, the image of `Spa(L, L⁺) → ∏ᵢ Spa(Aᵢ, Aᵢ⁺)` is the set of
families compatible with the maps `Spa(Aⱼ, Aⱼ⁺) → Spa(Aᵢ, Aᵢ⁺)` induced by the `tᵢⱼ`. -/
theorem range_pi_spaComap :
    Set.range (fun (v : spa Lplus) i ↦ spaComap (φ i) (hφc i) (Aplus i) Lplus (hφplus i) v) =
      {w : ∀ i, spa (Aplus i) | ∀ i j (h : i ≤ j),
        spaComap (t i j h) (ht i j h) (Aplus i) (Aplus j) (htplus i j h) (w j) = w i} := by
  refine Set.Subset.antisymm ?_ fun w hw ↦ ?_
  · rintro _ ⟨v, rfl⟩ i j h
    refine Subtype.ext ?_
    simp only [spaComap_val]
    exact comap_comap_of_comp_eq hφt h v.1
  have hw' : (fun i ↦ (w i).1) ∈
      {w : ∀ i, Spv (A i) | ∀ i j (h : i ≤ j), comap (t i j h) (w j) = w i} :=
    fun i j h ↦ (spaComap_val _ _ _ _ _ _).symm.trans (congrArg Subtype.val (hw i j h))
  rw [← range_pi_comap hφt hcover hker] at hw'
  obtain ⟨v, hv⟩ := hw'
  have hvi : ∀ i, comap (φ i) v = (w i).1 := fun i ↦ congr_fun hv i
  have hmem : v ∈ spa Lplus :=
    (mem_spa_iff_forall_comap_mem_spa Aplus Lplus hφc hφplus hφt hcover ht P hP hLplus v).mpr
      fun i ↦ hvi i ▸ (w i).2
  exact ⟨⟨v, hmem⟩, funext fun i ↦ Subtype.ext ((spaComap_val _ _ _ _ _ _).trans (hvi i))⟩

/-- **The adic spectrum of a directed colimit of Huber pairs is the inverse limit of the adic
spectra of the stages.** Under the hypotheses of `range_pi_spaComap`, pulling back along the
`φᵢ` is a homeomorphism of `Spa(L, L⁺)` onto the space of compatible families of points of the
`Spa(Aᵢ, Aᵢ⁺)`. -/
noncomputable def spaDirectLimitHomeomorph :
    spa Lplus ≃ₜ {w : ∀ i, spa (Aplus i) | ∀ i j (h : i ≤ j),
      spaComap (t i j h) (ht i j h) (Aplus i) (Aplus j) (htplus i j h) (w j) = w i} :=
  (isEmbedding_pi_spaComap Aplus Lplus hφc hφplus hφt hcover).toHomeomorph.trans
    (Homeomorph.setCongr
      (range_pi_spaComap Aplus Lplus hφc hφplus hφt hcover ht htplus hker P hP hLplus))

/-- The `i`-th coordinate of `spaDirectLimitHomeomorph` is the pullback along `φᵢ`. -/
@[simp]
theorem spaDirectLimitHomeomorph_apply_coe (v : spa Lplus) (i : ι) :
    (spaDirectLimitHomeomorph Aplus Lplus hφc hφplus hφt hcover ht htplus hker P hP hLplus v :
      ∀ i, spa (Aplus i)) i = spaComap (φ i) (hφc i) (Aplus i) Lplus (hφplus i) v :=
  (rfl)

/-- The point of `Spa(L, L⁺)` glued from a compatible family pulls back to the `i`-th member of
the family along `φᵢ`. -/
@[simp]
theorem spaComap_spaDirectLimitHomeomorph_symm_apply
    (w : {w : ∀ i, spa (Aplus i) | ∀ i j (h : i ≤ j),
      spaComap (t i j h) (ht i j h) (Aplus i) (Aplus j) (htplus i j h) (w j) = w i}) (i : ι) :
    spaComap (φ i) (hφc i) (Aplus i) Lplus (hφplus i)
        ((spaDirectLimitHomeomorph Aplus Lplus hφc hφplus hφt hcover ht htplus hker P hP
          hLplus).symm w) = (w : ∀ i, spa (Aplus i)) i := by
  rw [← spaDirectLimitHomeomorph_apply_coe Aplus Lplus hφc hφplus hφt hcover ht htplus hker P hP
    hLplus, Homeomorph.apply_symm_apply]

end Spa

section Rational

variable [IsDirectedOrder ι] (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)
  (hcover : ∀ x : L, ∃ i a, φ i a = x)

variable (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)

include hφt hcover hker in
/-- **Rational subsets of the adic spectrum of a colimit come from a finite stage.** For finite
`T ⊆ L` and `s ∈ L`, there are a stage `i`, a finite `T' ⊆ Aᵢ` and `s' ∈ Aᵢ` such that the
rational subset `R(T/s)` of `Spa(L, L⁺)` is the preimage of `R(T'/s')` under
`Spa(L, L⁺) → Spa(Aᵢ, Aᵢ⁺)`. If `T` generates the unit ideal of `L`, then `T'` can be chosen to
generate the unit ideal of `Aᵢ`. -/
theorem exists_spaComap_preimage_rationalSubset (Aplus : ∀ i, Subring (A i))
    (Lplus : Subring L) (hφc : ∀ i, Continuous (φ i))
    (hφplus : ∀ i, ∀ a ∈ Aplus i, φ i a ∈ Lplus) (T : Finset L) (s : L) :
    ∃ i, ∃ (T' : Finset (A i)) (s' : A i),
      (Ideal.span (T : Set L) = ⊤ → Ideal.span (T' : Set (A i)) = ⊤) ∧
      Subtype.val ⁻¹' rationalSubset Lplus T s =
        spaComap (φ i) (hφc i) (Aplus i) Lplus (hφplus i) ⁻¹'
          (Subtype.val ⁻¹' rationalSubset (Aplus i) T' s') := by
  classical
  -- the preimage of `R(T'/s')` is `R(φᵢ(T')/φᵢ(s'))`, so it suffices to lift `T` and `s`
  suffices h : ∃ i, ∃ (T' : Finset (A i)) (s' : A i), T'.image (φ i) = T ∧ φ i s' = s ∧
      (Ideal.span (T : Set L) = ⊤ → Ideal.span (T' : Set (A i)) = ⊤) by
    obtain ⟨i, T', s', hT, hs, hspan⟩ := h
    refine ⟨i, T', s', hspan, ?_⟩
    rw [spaComap_preimage_rationalSubset, hT, hs]
  by_cases hT : Ideal.span (T : Set L) = ⊤
  · -- lift `s`, `T` and the coefficients of a relation `∑ cₓ x = 1`, then wait for the relation
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp (hT ▸ Submodule.mem_top : (1 : L) ∈ _)
    obtain ⟨i, g, hg⟩ := exists_lift hφt hcover (insert s (T ∪ T.image c))
    have hgT : ∀ x ∈ T, φ i (g x) = x := fun x hx ↦ hg x (by simp [hx])
    have hgc : ∀ x ∈ T, φ i (g (c x)) = c x := fun x hx ↦
      hg _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem c hx)))
    have hsum : φ i (∑ x ∈ T, g (c x) * g x) = φ i 1 := by
      rw [map_sum, map_one, ← hc]
      exact Finset.sum_congr rfl fun x hx ↦ by rw [map_mul, hgc x hx, hgT x hx, smul_eq_mul]
    obtain ⟨j, hij, hj⟩ := hker i _ _ hsum
    refine ⟨j, T.image (t i j hij ∘ g), t i j hij (g s), ?_, ?_, fun _ ↦ ?_⟩
    · rw [Finset.image_image]
      refine (Finset.image_congr fun x hx ↦ ?_).trans T.image_id
      simp only [Function.comp_apply, hφt, hgT x hx, id]
    · rw [hφt, hg s (Finset.mem_insert_self _ _)]
    · rw [Ideal.eq_top_iff_one, ← map_one (t i j hij), ← hj, map_sum]
      refine sum_mem fun x hx ↦ ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_image_of_mem _ hx))
  · obtain ⟨i, g, hg⟩ := exists_lift hφt hcover (insert s T)
    refine ⟨i, T.image g, g s, ?_, hg s (Finset.mem_insert_self _ _), fun h ↦ absurd h hT⟩
    rw [Finset.image_image]
    exact (Finset.image_congr fun x hx ↦ hg x (Finset.mem_insert_of_mem hx)).trans T.image_id

end Rational

end TauCeti.ValuationSpectrum
