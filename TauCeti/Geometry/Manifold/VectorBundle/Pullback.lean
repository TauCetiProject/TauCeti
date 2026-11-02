/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Regularity and functoriality of pullback bundles

A map into the total space of a pullback bundle is smooth exactly when its projection to the new
base and its lift to the original total space are smooth. This is the smooth analogue of the
initial-topology description of a pullback bundle.

The criterion lets a map into a pullback bundle be checked without unfolding the pulled-back
trivializations. It is particularly useful for tangent maps whose base points agree through a
commuting square.

The criterion applies to fibre bundles with a normed model fibre; the fibres themselves need
only be nonempty topological spaces, without an additive or vector-space structure.

The file also records the functoriality of Mathlib's pullback `f *ᵖ E` in `C^n` maps `f`, on its
own carrier. The canonical map `Pullback.lift f` to the total space of `E` is `C^n`
(`Bundle.Pullback.contMDiff_lift`), and a family of fibrewise maps inducing a `C^n` map of total
spaces pulls back along a `C^n` map to one that does too (`Bundle.Pullback.contMDiff_fiberwise`).
When the model fibre is finite-dimensional over a complete field `𝕜`, `TauCeti.bundleDiffeomorph`
and the fibre instances of `TauCeti.Topology.VectorBundle.Pullback` therefore make the pullback
`x ↦ e (f x)` of a `C^n` family `e` of fibrewise linear equivalences again a `C^n` bundle
equivalence. The pullback along the identity is `C^n` diffeomorphic to `E`
(`Bundle.Pullback.idDiffeomorph`), and the pullback along a composite `g ∘ f` to the iterated
pullback `f *ᵖ (g *ᵖ E)` (`Bundle.Pullback.compDiffeomorph`), whatever the regularity of the
maps pulled back along. Both comparisons are the identity on every fibre, so for vector bundles
they are fibrewise linear, and over a complex model at `n = ∞` they are holomorphic bundle
equivalences between holomorphic vector bundles, which Mathlib's `ContMDiffVectorBundle.pullback`
makes `f *ᵖ E` when `E` is one.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

open Bundle
open scoped Manifold

namespace Bundle.Pullback

variable {𝕜 F EM EM' EX H H' HX B B' X K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [NormedAddCommGroup EM'] [NormedSpace 𝕜 EM']
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace HX]
  {I : ModelWithCorners 𝕜 EM H} {I' : ModelWithCorners 𝕜 EM' H'}
  {IX : ModelWithCorners 𝕜 EX HX}
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace B'] [ChartedSpace H' B']
  [TopologicalSpace X] [ChartedSpace HX X]
  {E : B → Type*} [∀ x, Nonempty (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [FunLike K B' B] [ContinuousMapClass K B' B] {n : WithTop ℕ∞}

/-- A map into a pullback bundle is `C^n` at a point exactly when its base projection and its
lift to the original total space are `C^n` there. -/
theorem contMDiffAt_iff (f : K) {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} {x : X}
    (hf : ContMDiffAt I' I n f (q x).proj) :
    ContMDiffAt IX (I'.prod 𝓘(𝕜, F)) n q x ↔
      ContMDiffAt IX I' n (fun y => (q y).proj) x ∧
        ContMDiffAt IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) x := by
  simp only [Bundle.contMDiffAt_totalSpace, trivializationAt,
    FiberBundle.pullback_trivializationAt', Trivialization.pullback_apply, Pullback.lift_proj]
  exact ⟨fun ⟨hq, hcoord⟩ => ⟨hq, hf.comp x hq, hcoord⟩,
    fun ⟨hq, _, hcoord⟩ => ⟨hq, hcoord⟩⟩

/-- A map into a pullback bundle is `C^n` exactly when its base projection and its lift to the
original total space are `C^n`. -/
theorem contMDiff_iff (f : K) (hf : ContMDiff I' I n f)
    {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} :
    ContMDiff IX (I'.prod 𝓘(𝕜, F)) n q ↔
      ContMDiff IX I' n (fun y => (q y).proj) ∧
        ContMDiff IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) := by
  simp only [ContMDiff, ← forall_and]
  exact forall_congr' fun x => contMDiffAt_iff f hf.contMDiffAt

/-- The canonical map `Pullback.lift f` from the total space of a pullback bundle to the original
total space is `C^n` at every point over which `f` is `C^n`. -/
theorem contMDiffAt_lift (f : K) {p : TotalSpace F ((f : B' → B) *ᵖ E)}
    (hf : ContMDiffAt I' I n f p.proj) :
    ContMDiffAt (I'.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) n (Pullback.lift f) p :=
  ((contMDiffAt_iff f hf).1 contMDiffAt_id).2

/-- The canonical map `Pullback.lift f` from the total space of a pullback bundle to the original
total space is `C^n` when `f` is. -/
theorem contMDiff_lift (f : K) (hf : ContMDiff I' I n f) :
    ContMDiff (I'.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) n
      (Pullback.lift f : TotalSpace F ((f : B' → B) *ᵖ E) → TotalSpace F E) :=
  fun p ↦ contMDiffAt_lift f (hf p.proj)

/-- Pulling back is natural: if a family `φ` of fibrewise maps from `E` to `E'` induces a `C^n` map
of total spaces, then so does the family `x ↦ φ (f x)` pulled back along a `C^n` map `f`, from
`f *ᵖ E` to `f *ᵖ E'`. The fibrewise maps need not be linear. -/
theorem contMDiff_fiberwise {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {E' : B → Type*} [∀ x, Nonempty (E' x)] [∀ x, TopologicalSpace (E' x)]
    [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E'] (φ : ∀ b, E b → E' b)
    (hφ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (φ p.proj p.2))
    (f : K) (hf : ContMDiff I' I n f) :
    ContMDiff (I'.prod 𝓘(𝕜, F)) (I'.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F ((f : B' → B) *ᵖ E) ↦
        TotalSpace.mk' F' (E := (f : B' → B) *ᵖ E') p.proj (φ (f p.proj) p.2) :=
  (contMDiff_iff f hf).2 ⟨contMDiff_proj _, hφ.comp (contMDiff_lift f hf)⟩

variable (E) in
/-- The pullback of a bundle along the identity is the bundle itself: the canonical map
`Pullback.lift` is a `C^n` diffeomorphism of total spaces, the identity on every fibre. Over a
complex model at `n = ∞` this is a biholomorphism of total spaces. -/
def idDiffeomorph {m : WithTop ℕ∞} :
    TotalSpace F ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E) ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯
      TotalSpace F E where
  toFun := Pullback.lift ContMDiffMap.id
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_lift _ contMDiff_id
  contMDiff_invFun := (contMDiff_iff _ contMDiff_id).2 ⟨contMDiff_proj E, contMDiff_id⟩

@[simp]
theorem idDiffeomorph_apply {m : WithTop ℕ∞}
    (p : TotalSpace F ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E)) :
    idDiffeomorph (I := I) (n := n) E p = ⟨p.proj, p.2⟩ :=
  (rfl)

@[simp]
theorem idDiffeomorph_symm_apply {m : WithTop ℕ∞} (p : TotalSpace F E) :
    (idDiffeomorph (I := I) (m := m) (n := n) E).symm p = ⟨p.proj, p.2⟩ :=
  (rfl)

variable {EM'' H'' B'' : Type*} [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM'']
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 EM'' H''}
  [TopologicalSpace B''] [ChartedSpace H'' B''] {m : WithTop ℕ∞}

variable (E) in
/-- Pulling back along a composite is pulling back in two steps: for `C^m` maps
`f : B'' → B'` and `g : B' → B`, the total spaces of `(g ∘ f) *ᵖ E` and `f *ᵖ (g *ᵖ E)` are
`C^n` diffeomorphic, for any `m` and `n`, by the identity on every fibre `E (g (f x))`. -/
def compDiffeomorph (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) :
    TotalSpace F ((g.comp f : B'' → B) *ᵖ E) ≃ₘ^n⟮I''.prod 𝓘(𝕜, F), I''.prod 𝓘(𝕜, F)⟯
      TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  -- Both total spaces are charted at `p` by the trivialization of `E` at `g (f p.proj)`, so in
  -- these coordinates the map is the identity, whatever the regularity of `f` and `g`.
  contMDiff_toFun p := contMDiffAt_totalSpace.2
    ⟨contMDiffAt_proj _, (contMDiffAt_totalSpace.1 (contMDiffAt_id (x := p))).2⟩
  contMDiff_invFun p := contMDiffAt_totalSpace.2
    ⟨contMDiffAt_proj _, (contMDiffAt_totalSpace.1 (contMDiffAt_id (x := p))).2⟩

@[simp]
theorem compDiffeomorph_apply (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯)
    (p : TotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    compDiffeomorph (n := n) E g f p = ⟨p.proj, p.2⟩ :=
  (rfl)

@[simp]
theorem compDiffeomorph_symm_apply (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯)
    (p : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (compDiffeomorph (n := n) E g f).symm p = ⟨p.proj, p.2⟩ :=
  (rfl)

/-- Under `compDiffeomorph`, the canonical map of the composite pullback is the composite of the
canonical maps of the two steps. -/
theorem lift_comp_compDiffeomorph (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) :
    Pullback.lift (F := F) (E := E) g ∘ Pullback.lift f ∘ compDiffeomorph (n := n) E g f =
      Pullback.lift (g.comp f) :=
  (rfl)

end Bundle.Pullback
