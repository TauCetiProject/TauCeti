/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination

/-!
# Images and composition of semialgebraic functions

Let `R` be a commutative ring with a compatible linear order, and suppose that semialgebraic sets
are closed under projection: for every semialgebraic `s ⊆ R ^ (n + 1)`, the image
`Fin.tail '' s ⊆ R ^ n` forgetting coordinate `0` is semialgebraic
(`TauCeti.HasSemialgebraicProjections R`). For `ℝ` this is the Tarski–Seidenberg theorem, an
instance proved in `TauCeti.Geometry.RealAlgebraic.CAD.Existence`, so every result below holds
over `ℝ` unconditionally. This file develops the parts of the theory of semialgebraic sets and
functions that need projection.

Eliminating one coordinate at a time, the projection of a semialgebraic subset of `σ ⊕ τ → R` onto
the coordinates `τ` is semialgebraic whenever `σ` is finite. Since the graph of a function
`f : (σ → R) → (τ → R)` is encoded as a subset of `σ ⊕ τ → R` (`TauCeti.IsSemialgebraicOn`), this
gives the following consequences.

* The image of a semialgebraic set under a semialgebraic function with finitely many input
  coordinates is semialgebraic, and so is the inverse image of a semialgebraic set under a
  semialgebraic function with finitely many output coordinates.
* The domain of a function with finitely many output coordinates and semialgebraic graph is the
  projection of that graph, so it is semialgebraic: the domain hypothesis in
  `TauCeti.IsSemialgebraicOn` becomes redundant.
* Semialgebraic functions compose when the intermediate space has finitely many coordinates: the
  graph of `g ∘ f` is obtained from the graphs of `f` and `g` by eliminating the intermediate
  coordinates.

## Main results

All results assume projection closure, `[TauCeti.HasSemialgebraicProjections R]`.

* `TauCeti.IsSemialgebraic.image_comp_inr`, `TauCeti.IsSemialgebraic.image_comp_inl`: projections
  of semialgebraic sets that forget finitely many coordinates are semialgebraic.
* `TauCeti.IsSemialgebraicOn.isSemialgebraic_image`,
  `TauCeti.IsSemialgebraicMap.isSemialgebraic_image`: images under semialgebraic functions with
  finitely many input coordinates; `TauCeti.IsSemialgebraic.image_eval`: images under polynomial
  maps with finitely many input and output coordinates.
* `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_preimage`,
  `TauCeti.IsSemialgebraicMap.isSemialgebraic_preimage`: inverse images under semialgebraic
  functions with finitely many output coordinates.
* `TauCeti.isSemialgebraicOn_iff_graph`: a function with finitely many output coordinates is
  semialgebraic on `s` exactly when its graph over `s` is semialgebraic.
* `TauCeti.IsSemialgebraicOn.comp`, `TauCeti.IsSemialgebraicMap.comp`: composition, when the
  intermediate space has finitely many coordinates.

## References

* S. Basu, R. Pollack, and M.-F. Roy,
  [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
  second edition, Chapter 2.
* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Section 2.2.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ υ R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `σ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inr [Finite σ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s) := by
  revert τ
  refine Finite.induction_empty_option
    (P := fun σ => ∀ {τ : Type _} {s : Set (σ ⊕ τ → R)}, IsSemialgebraic s →
      IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s))
    (fun {α β} e ih {τ} {s} hs => ?_) (fun {τ} {s} hs => ?_)
    (fun {α} _ ih {τ} {s} hs => ?_) σ
  · -- Transport along `e : α ≃ β` in the coordinates to be forgotten.
    convert ih (hs.preimage_comp (Equiv.sumCongr e.symm (Equiv.refl τ))) using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z ∘ Equiv.sumCongr e (Equiv.refl τ), ?_, rfl⟩
      convert hz using 1
      ext (b | c) <;> simp
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hz, rfl⟩
  · -- With no coordinates to forget, the projection is the bijection `Sum.inr`.
    convert hs.preimage_comp (Equiv.emptySum PEmpty τ) using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      convert hz using 1
      ext (b | c)
      · exact b.elim
      · rfl
    · intro hy
      exact ⟨_, hy, rfl⟩
  · -- Forget the coordinate `none` with `IsSemialgebraic.image_comp_some`, then the coordinates
    -- `α` by induction.
    let k : Option α ⊕ τ → Option (α ⊕ τ) :=
      Sum.elim (Option.elim · none (some ∘ Sum.inl)) (some ∘ Sum.inr)
    convert ih (hs.preimage_comp k).image_comp_some using 1
    ext y
    simp only [mem_image, mem_preimage, exists_exists_and_eq_and]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(Option.elim · (z (.inl none)) (z ∘ Sum.elim (Sum.inl ∘ some) Sum.inr)), ?_, rfl⟩
      convert hz using 1
      ext ((_ | a) | c) <;> rfl
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, hw, rfl⟩

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `τ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inl [Finite τ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inl) '' s) := by
  convert (hs.preimage_comp (Equiv.sumComm σ τ)).image_comp_inr using 1
  ext y
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z ∘ Equiv.sumComm τ σ, ?_, rfl⟩
    convert hz using 1
    ext (a | b) <;> rfl
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, rfl⟩

/-- Given projection closure, the image of the domain of a semialgebraic function with finitely
many input coordinates is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_image [Finite σ] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) : IsSemialgebraic (f '' s) := by
  convert hf.graph.image_comp_inr using 1
  ext y
  simp only [mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Sum.elim x (f x), ⟨hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hfz⟩, rfl⟩
    exact ⟨_, hz, hfz⟩

/-- Given projection closure, the image of a semialgebraic set under a semialgebraic map with
finitely many input coordinates is semialgebraic. -/
theorem IsSemialgebraicMap.isSemialgebraic_image [Finite σ] {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (f '' s) :=
  (hf.isSemialgebraicOn hs).isSemialgebraic_image

/-- Given projection closure, the image of a semialgebraic set under a polynomial map with finitely
many input coordinates and finitely many output coordinates is semialgebraic. -/
theorem IsSemialgebraic.image_eval [Finite σ] [Finite τ] {s : Set (σ → R)}
    (hs : IsSemialgebraic s) (p : τ → MvPolynomial σ R) :
    IsSemialgebraic ((fun x i => eval x (p i)) '' s) :=
  (isSemialgebraicOn_eval p hs).isSemialgebraic_image

/-- Given projection closure, the points of the domain of a semialgebraic function with finitely
many output coordinates at which it takes values in a semialgebraic set form a semialgebraic
set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_preimage [Finite τ] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) {t : Set (τ → R)} (ht : IsSemialgebraic t) :
    IsSemialgebraic (s ∩ f ⁻¹' t) := by
  convert (hf.graph.inter (ht.preimage_comp Sum.inr)).image_comp_inl using 1
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨Sum.elim x (f x), ⟨⟨hx, rfl⟩, hfx⟩, rfl⟩
  · rintro ⟨z, ⟨⟨hz, hfz⟩, hzt⟩, rfl⟩
    exact ⟨hz, by rw [mem_preimage, hfz]; exact hzt⟩

/-- Given projection closure, the inverse image of a semialgebraic set under a semialgebraic map
with finitely many output coordinates is semialgebraic. -/
theorem IsSemialgebraicMap.isSemialgebraic_preimage [Finite τ] {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {t : Set (τ → R)} (ht : IsSemialgebraic t) :
    IsSemialgebraic (f ⁻¹' t) := by
  simpa using (isSemialgebraicOn_univ.2 hf).isSemialgebraic_inter_preimage ht

/-- Given projection closure, a function with finitely many output coordinates is semialgebraic on
`s` if and only if its graph over `s` is semialgebraic: the domain `s` is the projection of the
graph. -/
theorem isSemialgebraicOn_iff_graph [Finite τ] {f : (σ → R) → (τ → R)} {s : Set (σ → R)} :
    IsSemialgebraicOn f s ↔
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) := by
  refine ⟨IsSemialgebraicOn.graph, fun h => isSemialgebraicOn_def.2 ⟨?_, h⟩⟩
  convert h.image_comp_inl using 1
  ext x
  simp only [mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · intro hx
    exact ⟨Sum.elim x (f x), ⟨hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨hz, -⟩, rfl⟩
    exact hz

/-- Given projection closure, the composition of semialgebraic functions is semialgebraic: if `f`
is semialgebraic on `s` and maps it into `t`, and `g` is semialgebraic on `t`, then `g ∘ f` is
semialgebraic on `s`. The intermediate space has finitely many coordinates. -/
theorem IsSemialgebraicOn.comp [Finite τ] {g : (τ → R) → (υ → R)} {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} {t : Set (τ → R)} (hg : IsSemialgebraicOn g t)
    (hf : IsSemialgebraicOn f s) (hst : MapsTo f s t) : IsSemialgebraicOn (g ∘ f) s := by
  refine isSemialgebraicOn_def.2 ⟨hf.isSemialgebraic, ?_⟩
  -- In the coordinates `τ ⊕ (σ ⊕ υ)`, cut out the points `(f x, x, g (f x))` with `x ∈ s` and
  -- forget the intermediate coordinates `τ`.
  convert ((hf.graph.preimage_comp (Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl)).inter
    (hg.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))).image_comp_inr using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
  constructor
  · rintro ⟨hz, hgz⟩
    exact ⟨Sum.elim (f (z ∘ Sum.inl)) z,
      ⟨mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hz, rfl⟩,
        mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hst hz, hgz⟩⟩, rfl⟩
  · rintro ⟨w, ⟨hwf, hwg⟩, rfl⟩
    obtain ⟨hw, hfw⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 hwf
    obtain ⟨-, hgw⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 hwg
    exact ⟨hw, (congrArg g hfw).trans hgw⟩

/-- Given projection closure, the composition of semialgebraic maps is semialgebraic when the
intermediate space has finitely many coordinates. -/
theorem IsSemialgebraicMap.comp [Finite τ] {g : (τ → R) → (υ → R)} {f : (σ → R) → (τ → R)}
    (hg : IsSemialgebraicMap g) (hf : IsSemialgebraicMap f) : IsSemialgebraicMap (g ∘ f) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hg).comp
    (isSemialgebraicOn_univ.2 hf) (mapsTo_univ f univ)

end TauCeti
