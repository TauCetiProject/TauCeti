/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Comp
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Local

/-!
# Locally semialgebraic sets and Nash germs

Locally semialgebraic sets (`TauCeti.IsLocallySemialgebraic`) are the sets of the Nash category:
near every point they are cut out by sign conditions on Nash germs, and their preimages under Nash
maps are again locally semialgebraic. This file proves both facts.

A map `g : (σ → ℝ) → (τ → ℝ)` is treated as a Nash map germ at `x` when each of its coordinates is
a Nash germ at `x` (`TauCeti.IsNashAt`). The preimage of a set semialgebraic at `g x` under such a
map is semialgebraic at `x`, since the graph of `g` is semialgebraic on a neighbourhood of `x`.
Consequently global Nash bijections between coordinate spaces, whose inverses are also Nash,
transport locally semialgebraic sets.

We record the finite Boolean combinations of zero sets `{y | f y = 0}` and positivity sets
`{y | 0 < f y}` of functions `f` that are Nash germs at every point of `U` as
`TauCeti.IsNashBooleanCombination U t`, in the same way as
`TauCeti.IsAnalyticBooleanCombination` for analytic functions. A set is semialgebraic at `x`
exactly when, on a neighbourhood `U` of `x`, it agrees with such a combination, and every such
combination is described by a condition on the signs of finitely many such functions. One direction
holds because polynomials are Nash germs everywhere; for the other, every Nash germ has
semialgebraic graph near its point, so its zero and positivity sets are semialgebraic at that point.

## Main declarations

* `TauCeti.IsNashBooleanCombination U t`: `t` is a finite Boolean combination of zero sets and
  positivity sets of functions that are Nash germs at every point of `U`.

## Main results

* `TauCeti.SemialgebraicAt.preimage`, `TauCeti.IsLocallySemialgebraic.preimage`: preimages under
  maps with Nash coordinates.
* `Equiv.semialgebraicAt_image_iff`, `Equiv.isLocallySemialgebraic_image_iff`: invariance under
  bijections that are Nash with Nash inverses.
* `TauCeti.IsNashAt.semialgebraicAt_setOf_eq_zero`, `TauCeti.IsNashAt.semialgebraicAt_setOf_pos`:
  the zero and positivity sets of a Nash germ at `x` are semialgebraic at `x`.
* `TauCeti.IsNashBooleanCombination.exists_eq_setOf_sign`: the sign-condition normal form of a
  Boolean combination of Nash sign conditions.
* `TauCeti.semialgebraicAt_iff_exists_isNashBooleanCombination`: a set is semialgebraic at `x` if
  and only if near `x` it agrees with a finite Boolean combination of sign conditions on functions
  that are Nash germs on a neighbourhood of `x`.
* `TauCeti.IsNashBooleanCombination.preimage`: preimages of these combinations under maps with
  Nash coordinates, and `TauCeti.IsNashBooleanCombination.isAnalyticBooleanCombination`: they are in
  particular Boolean combinations of analytic sign conditions.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
-/

public section

open Filter MeasureTheory MvPolynomial Set Topology

namespace TauCeti

variable {σ τ : Type*} [Fintype σ]

/-! ### Preimages under Nash maps -/

/-- **Nash preimages.** The preimage of a set semialgebraic at `g x` under a map `g` whose
coordinates are Nash germs at `x` is semialgebraic at `x`. -/
theorem SemialgebraicAt.preimage [Finite τ] {s : Set (τ → ℝ)} {g : (σ → ℝ) → (τ → ℝ)} {x : σ → ℝ}
    (hs : SemialgebraicAt s (g x)) (hg : ∀ i, IsNashAt (fun y ↦ g y i) x) :
    SemialgebraicAt (g ⁻¹' s) x := by
  cases nonempty_fintype τ
  obtain ⟨hga, W, hWo, hxW, hgW⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hg
  obtain ⟨U, hUo, hgxU, -, hsU⟩ := semialgebraicAt_def.mp hs
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp <| inter_mem (hWo.mem_nhds hxW)
    (hga.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgxU))
  refine semialgebraicAt_iff_exists_ball.mpr ⟨ε, hε, ?_⟩
  convert (hgW.isSemialgebraic_inter_preimage hsU).inter (isSemialgebraic_ball x ε) using 1
  ext y
  simp only [mem_inter_iff, mem_preimage]
  exact ⟨fun ⟨hy, hyε⟩ ↦ ⟨⟨(hεV hyε).1, hy, (hεV hyε).2⟩, hyε⟩,
    fun ⟨⟨_, hy, _⟩, hyε⟩ ↦ ⟨hy, hyε⟩⟩

/-- **Nash preimages.** The preimage of a locally semialgebraic set under a map whose coordinates
are Nash germs at every point is locally semialgebraic. -/
theorem IsLocallySemialgebraic.preimage [Finite τ] {s : Set (τ → ℝ)} (hs : IsLocallySemialgebraic s)
    {g : (σ → ℝ) → (τ → ℝ)} (hg : ∀ x i, IsNashAt (fun y ↦ g y i) x) :
    IsLocallySemialgebraic (g ⁻¹' s) :=
  isLocallySemialgebraic_iff.mpr fun x ↦ (hs.semialgebraicAt (g x)).preimage (hg x)

/-- **Nash isomorphisms, locally.** For a bijection `e` whose coordinates are Nash germs at `x`
and whose inverse has coordinates that are Nash germs at `e x`, the image `e '' s` is semialgebraic
at `e x` if and only if `s` is semialgebraic at `x`. -/
theorem _root_.Equiv.semialgebraicAt_image_iff [Fintype τ] {s : Set (σ → ℝ)} {x : σ → ℝ}
    (e : (σ → ℝ) ≃ (τ → ℝ)) (he : ∀ i, IsNashAt (fun y ↦ e y i) x)
    (he' : ∀ i, IsNashAt (fun y ↦ e.symm y i) (e x)) :
    SemialgebraicAt (e '' s) (e x) ↔ SemialgebraicAt s x := by
  rw [e.image_eq_preimage_symm]
  refine ⟨fun hs ↦ ?_, fun hs ↦ .preimage (by rwa [e.symm_apply_apply]) he'⟩
  simpa [preimage_preimage] using hs.preimage he

/-- **Nash isomorphisms.** For a bijection `e` whose coordinates and whose inverse's coordinates
are Nash germs at every point, the image `e '' s` is locally semialgebraic if and only if `s` is
locally semialgebraic. -/
theorem _root_.Equiv.isLocallySemialgebraic_image_iff [Fintype τ] {s : Set (σ → ℝ)}
    (e : (σ → ℝ) ≃ (τ → ℝ)) (he : ∀ x i, IsNashAt (fun y ↦ e y i) x)
    (he' : ∀ x i, IsNashAt (fun y ↦ e.symm y i) x) :
    IsLocallySemialgebraic (e '' s) ↔ IsLocallySemialgebraic s := by
  rw [e.image_eq_preimage_symm]
  refine ⟨fun hs ↦ ?_, fun hs ↦ hs.preimage he'⟩
  simpa [preimage_preimage] using hs.preimage he

/-! ### Sign conditions on Nash germs -/

/-- The zero set of a Nash germ at `x` is semialgebraic at `x`. -/
theorem IsNashAt.semialgebraicAt_setOf_eq_zero {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) : SemialgebraicAt {y | f y = 0} x := by
  simpa using ((isSemialgebraic_eval_eq_zero (X () : MvPolynomial Unit ℝ)).semialgebraicAt _
    ).preimage (g := fun y _ ↦ f y) fun _ ↦ hf

/-- The positivity set of a Nash germ at `x` is semialgebraic at `x`. -/
theorem IsNashAt.semialgebraicAt_setOf_pos {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) : SemialgebraicAt {y | 0 < f y} x := by
  simpa using ((isSemialgebraic_eval_pos (X () : MvPolynomial Unit ℝ)).semialgebraicAt _
    ).preimage (g := fun y _ ↦ f y) fun _ ↦ hf

/-! ### Finite Boolean combinations of Nash sign conditions -/

/-- A set `t ⊆ σ → ℝ` is a *finite Boolean combination of Nash sign conditions on `U`* if it
belongs to the algebra of sets generated by the zero sets `{y | f y = 0}` and the positivity sets
`{y | 0 < f y}` of the real functions `f` that are Nash germs at every point of `U`. Only the part
of `t` inside `U` is meaningful for local semialgebraicity. -/
def IsNashBooleanCombination (U t : Set (σ → ℝ)) : Prop :=
  t ∈ generateSetAlgebra
    ({t | ∃ f : (σ → ℝ) → ℝ, (∀ y ∈ U, IsNashAt f y) ∧ t = {y | f y = 0}} ∪
      {t | ∃ f : (σ → ℝ) → ℝ, (∀ y ∈ U, IsNashAt f y) ∧ t = {y | 0 < f y}})

/-- A set is a finite Boolean combination of Nash sign conditions on `U` if and only if it belongs
to the algebra of sets generated by the zero sets and positivity sets of the functions that are
Nash germs at every point of `U`. -/
theorem isNashBooleanCombination_def {U t : Set (σ → ℝ)} :
    IsNashBooleanCombination U t ↔ t ∈ generateSetAlgebra
      ({t | ∃ f : (σ → ℝ) → ℝ, (∀ y ∈ U, IsNashAt f y) ∧ t = {y | f y = 0}} ∪
        {t | ∃ f : (σ → ℝ) → ℝ, (∀ y ∈ U, IsNashAt f y) ∧ t = {y | 0 < f y}}) :=
  Iff.rfl

/-- The zero set of a function that is a Nash germ at every point of `U` is a Boolean combination
of Nash sign conditions on `U`. -/
theorem isNashBooleanCombination_setOf_eq_zero {U : Set (σ → ℝ)} {f : (σ → ℝ) → ℝ}
    (hf : ∀ y ∈ U, IsNashAt f y) : IsNashBooleanCombination U {y | f y = 0} :=
  self_subset_generateSetAlgebra (Or.inl ⟨f, hf, rfl⟩)

/-- The positivity set of a function that is a Nash germ at every point of `U` is a Boolean
combination of Nash sign conditions on `U`. -/
theorem isNashBooleanCombination_setOf_pos {U : Set (σ → ℝ)} {f : (σ → ℝ) → ℝ}
    (hf : ∀ y ∈ U, IsNashAt f y) : IsNashBooleanCombination U {y | 0 < f y} :=
  self_subset_generateSetAlgebra (Or.inr ⟨f, hf, rfl⟩)

/-- The finite Boolean combinations of Nash sign conditions on `U` form an algebra of sets. -/
theorem isSetAlgebra_setOf_isNashBooleanCombination (U : Set (σ → ℝ)) :
    IsSetAlgebra {t : Set (σ → ℝ) | IsNashBooleanCombination U t} :=
  isSetAlgebra_generateSetAlgebra

/-- The finite Boolean combinations of Nash sign conditions on `U` form the smallest algebra of
sets containing the zero set and the positivity set of every function that is a Nash germ at every
point of `U`. -/
theorem setOf_isNashBooleanCombination_subset {U : Set (σ → ℝ)} {ℬ : Set (Set (σ → ℝ))}
    (hℬ : IsSetAlgebra ℬ)
    (eq_zero : ∀ f : (σ → ℝ) → ℝ, (∀ y ∈ U, IsNashAt f y) → {y | f y = 0} ∈ ℬ)
    (pos : ∀ f : (σ → ℝ) → ℝ, (∀ y ∈ U, IsNashAt f y) → {y | 0 < f y} ∈ ℬ) :
    {t : Set (σ → ℝ) | IsNashBooleanCombination U t} ⊆ ℬ :=
  hℬ.generateSetAlgebra_subset <| union_subset (fun _ ⟨f, hf, h⟩ ↦ h ▸ eq_zero f hf)
    (fun _ ⟨f, hf, h⟩ ↦ h ▸ pos f hf)

/-- The empty set is a Boolean combination of Nash sign conditions. -/
@[simp]
theorem isNashBooleanCombination_empty (U : Set (σ → ℝ)) :
    IsNashBooleanCombination U (∅ : Set (σ → ℝ)) :=
  (isSetAlgebra_setOf_isNashBooleanCombination U).empty_mem

/-- The whole space is a Boolean combination of Nash sign conditions. -/
@[simp]
theorem isNashBooleanCombination_univ (U : Set (σ → ℝ)) :
    IsNashBooleanCombination U (univ : Set (σ → ℝ)) :=
  (isSetAlgebra_setOf_isNashBooleanCombination U).univ_mem

/-- A semialgebraic set is a Boolean combination of Nash sign conditions on every set `U`, since
polynomial functions are Nash germs everywhere. -/
theorem IsSemialgebraic.isNashBooleanCombination {t : Set (σ → ℝ)} (ht : IsSemialgebraic t)
    (U : Set (σ → ℝ)) : IsNashBooleanCombination U t :=
  setOf_isSemialgebraic_subset (isSetAlgebra_setOf_isNashBooleanCombination U)
    (fun p ↦ isNashBooleanCombination_setOf_eq_zero fun _ _ ↦ p.isNashAt_eval)
    (fun p ↦ isNashBooleanCombination_setOf_pos fun _ _ ↦ p.isNashAt_eval) ht

namespace IsNashBooleanCombination

variable {U V t t' : Set (σ → ℝ)}

/-- The complement of a Boolean combination of Nash sign conditions is one. -/
theorem compl (ht : IsNashBooleanCombination U t) : IsNashBooleanCombination U tᶜ :=
  (isSetAlgebra_setOf_isNashBooleanCombination U).compl_mem ht

/-- The union of two Boolean combinations of Nash sign conditions is one. -/
theorem union (ht : IsNashBooleanCombination U t) (ht' : IsNashBooleanCombination U t') :
    IsNashBooleanCombination U (t ∪ t') :=
  (isSetAlgebra_setOf_isNashBooleanCombination U).union_mem ht ht'

/-- The intersection of two Boolean combinations of Nash sign conditions is one. -/
theorem inter (ht : IsNashBooleanCombination U t) (ht' : IsNashBooleanCombination U t') :
    IsNashBooleanCombination U (t ∩ t') :=
  (isSetAlgebra_setOf_isNashBooleanCombination U).inter_mem ht ht'

/-- The difference of two Boolean combinations of Nash sign conditions is one. -/
theorem sdiff (ht : IsNashBooleanCombination U t) (ht' : IsNashBooleanCombination U t') :
    IsNashBooleanCombination U (t \ t') :=
  (isSetAlgebra_setOf_isNashBooleanCombination U).sdiff_mem ht ht'

/-- A finite union of Boolean combinations of Nash sign conditions is one. -/
protected theorem biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {t : ι → Set (σ → ℝ)}
    (ht : ∀ i ∈ I, IsNashBooleanCombination U (t i)) :
    IsNashBooleanCombination U (⋃ i ∈ I, t i) := by
  simpa using (isSetAlgebra_setOf_isNashBooleanCombination U).biUnion_mem hI.toFinset
    fun i hi ↦ ht i (hI.mem_toFinset.1 hi)

/-- A finite intersection of Boolean combinations of Nash sign conditions is one. -/
protected theorem biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {t : ι → Set (σ → ℝ)}
    (ht : ∀ i ∈ I, IsNashBooleanCombination U (t i)) :
    IsNashBooleanCombination U (⋂ i ∈ I, t i) := by
  simpa using (isSetAlgebra_setOf_isNashBooleanCombination U).biInter_mem hI.toFinset
    fun i hi ↦ ht i (hI.mem_toFinset.1 hi)

/-- The union of a finite family of Boolean combinations of Nash sign conditions is one. -/
protected theorem iUnion {ι : Type*} [Finite ι] {t : ι → Set (σ → ℝ)}
    (ht : ∀ i, IsNashBooleanCombination U (t i)) :
    IsNashBooleanCombination U (⋃ i, t i) := by
  simpa using IsNashBooleanCombination.biUnion finite_univ fun i (_ : i ∈ univ) ↦ ht i

/-- The intersection of a finite family of Boolean combinations of Nash sign conditions is one. -/
protected theorem iInter {ι : Type*} [Finite ι] {t : ι → Set (σ → ℝ)}
    (ht : ∀ i, IsNashBooleanCombination U (t i)) :
    IsNashBooleanCombination U (⋂ i, t i) := by
  simpa using IsNashBooleanCombination.biInter finite_univ fun i (_ : i ∈ univ) ↦ ht i

/-- A Boolean combination of sign conditions of functions that are Nash germs on `U` is also one
for any smaller set `V ⊆ U`. -/
theorem mono (ht : IsNashBooleanCombination U t) (hVU : V ⊆ U) :
    IsNashBooleanCombination V t :=
  setOf_isNashBooleanCombination_subset (isSetAlgebra_setOf_isNashBooleanCombination V)
    (fun _ hf ↦ isNashBooleanCombination_setOf_eq_zero fun y hy ↦ hf y (hVU hy))
    (fun _ hf ↦ isNashBooleanCombination_setOf_pos fun y hy ↦ hf y (hVU hy)) ht

/-- The preimage of a Boolean combination of Nash sign conditions on `U` under a map `g` whose
coordinates are Nash germs at every point of `V`, and which maps `V` into `U`, is a Boolean
combination of Nash sign conditions on `V`. -/
theorem preimage [Fintype τ] {U t : Set (τ → ℝ)} (ht : IsNashBooleanCombination U t)
    {g : (σ → ℝ) → (τ → ℝ)} (hg : ∀ y ∈ V, ∀ i, IsNashAt (fun z ↦ g z i) y)
    (hgVU : MapsTo g V U) : IsNashBooleanCombination V (g ⁻¹' t) :=
  setOf_isNashBooleanCombination_subset
    ((isSetAlgebra_setOf_isNashBooleanCombination V).preimage g)
    (fun _ hf ↦ isNashBooleanCombination_setOf_eq_zero fun y hy ↦ (hf _ (hgVU hy)).comp (hg y hy))
    (fun _ hf ↦ isNashBooleanCombination_setOf_pos fun y hy ↦ (hf _ (hgVU hy)).comp (hg y hy)) ht

/-- A Boolean combination of Nash sign conditions on `U` is a Boolean combination of analytic sign
conditions on `U`. -/
theorem isAnalyticBooleanCombination (ht : IsNashBooleanCombination U t) :
    IsAnalyticBooleanCombination U t :=
  setOf_isNashBooleanCombination_subset (isSetAlgebra_setOf_isAnalyticBooleanCombination U)
    (fun _ hf ↦ isAnalyticBooleanCombination_setOf_eq_zero fun y hy ↦ (hf y hy).analyticAt)
    (fun _ hf ↦ isAnalyticBooleanCombination_setOf_pos fun y hy ↦ (hf y hy).analyticAt) ht

/-- A Boolean combination of Nash sign conditions on `U` is semialgebraic at every point of
`U`. -/
theorem semialgebraicAt (ht : IsNashBooleanCombination U t) {x : σ → ℝ} (hx : x ∈ U) :
    SemialgebraicAt t x :=
  setOf_isNashBooleanCombination_subset (isSetAlgebra_setOf_semialgebraicAt x)
    (fun _ hf ↦ (hf x hx).semialgebraicAt_setOf_eq_zero)
    (fun _ hf ↦ (hf x hx).semialgebraicAt_setOf_pos) ht

end IsNashBooleanCombination

/-- The set where a function that is a Nash germ at every point of `U` has a prescribed sign is a
Boolean combination of Nash sign conditions on `U`. -/
theorem isNashBooleanCombination_setOf_sign_eq {U : Set (σ → ℝ)} {f : (σ → ℝ) → ℝ}
    (hf : ∀ y ∈ U, IsNashAt f y) (ε : SignType) :
    IsNashBooleanCombination U {y | SignType.sign (f y) = ε} := by
  rcases ε with _ | _ | _
  · simpa only [SignType.zero_eq_zero, sign_eq_zero_iff] using
      isNashBooleanCombination_setOf_eq_zero hf
  · simpa only [SignType.neg_eq_neg_one, sign_eq_neg_one_iff, Pi.neg_apply, neg_pos] using
      isNashBooleanCombination_setOf_pos fun y hy ↦ (hf y hy).neg
  · simpa only [SignType.pos_eq_one, sign_eq_one_iff] using
      isNashBooleanCombination_setOf_pos hf

/-- A condition on the signs of finitely many functions that are Nash germs at every point of `U`
defines a Boolean combination of Nash sign conditions on `U`. -/
theorem isNashBooleanCombination_setOf_sign {U : Set (σ → ℝ)} {ι : Type*} [Finite ι]
    {f : ι → (σ → ℝ) → ℝ} (hf : ∀ i, ∀ y ∈ U, IsNashAt (f i) y) (Φ : (ι → SignType) → Prop) :
    IsNashBooleanCombination U {y | Φ fun i ↦ SignType.sign (f i y)} := by
  rw [setOf_apply_eq_biUnion_iInter (fun i y ↦ SignType.sign (f i y))]
  exact .biUnion (toFinite _) fun ε _ ↦
    .iInter fun i ↦ isNashBooleanCombination_setOf_sign_eq (hf i) (ε i)

/-- **Sign-condition normal form.** A Boolean combination of Nash sign conditions on `U` is
described by a condition on the signs of finitely many functions that are Nash germs at every
point of `U`. -/
theorem IsNashBooleanCombination.exists_eq_setOf_sign {U t : Set (σ → ℝ)}
    (ht : IsNashBooleanCombination U t) :
    ∃ (m : ℕ) (f : Fin m → (σ → ℝ) → ℝ), (∀ i, ∀ y ∈ U, IsNashAt (f i) y) ∧
      ∃ Φ : (Fin m → SignType) → Prop, t = {y | Φ fun i ↦ SignType.sign (f i y)} :=
  exists_eq_setOf_sign_of_mem_generateSetAlgebra ht

/-- **Nash presentations of locally semialgebraic sets.** A set is semialgebraic at `x` if and only
if on some neighbourhood `U` of `x` it agrees with a finite Boolean combination of zero sets and
positivity sets of functions that are Nash germs at every point of `U`. -/
theorem semialgebraicAt_iff_exists_isNashBooleanCombination {s : Set (σ → ℝ)} {x : σ → ℝ} :
    SemialgebraicAt s x ↔
      ∃ U ∈ 𝓝 x, ∃ t, IsNashBooleanCombination U t ∧ s ∩ U = t ∩ U := by
  constructor
  · intro hs
    obtain ⟨U, hUo, hxU, -, hsU⟩ := semialgebraicAt_def.mp hs
    exact ⟨U, hUo.mem_nhds hxU, s ∩ U, hsU.isNashBooleanCombination U, by
      rw [inter_assoc, inter_self]⟩
  · rintro ⟨U, hU, t, ht, hst⟩
    refine (ht.semialgebraicAt (mem_of_mem_nhds hU)).congr ?_
    filter_upwards [hU] with y hy
    have := Set.ext_iff.mp hst y
    simp only [mem_inter_iff, hy, and_true] at this
    exact propext this.symm

end TauCeti
