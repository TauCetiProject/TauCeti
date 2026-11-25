/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Trivialization
import Mathlib.Geometry.Manifold.PartitionOfUnity

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

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

Along a local diffeomorphism `f`, regularity of sections can be read upstairs: a section `σ` of
`E` is `C^m` at `f x` exactly when its pullback `y ↦ σ (f y)`, a section of `f *ᵖ E`, is `C^m` at
`x` (`IsLocalDiffeomorphAt.contMDiffAt_section_iff_pullback`), and for a surjective local
diffeomorphism, such as the orbit projection of a free properly discontinuous action, a section
is `C^m` exactly when its pullback is (`IsLocalDiffeomorph.contMDiff_section_iff_pullback`).

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

The local chart comparison `Bundle.Pullback.localTransport` is smooth on the common chart
domain. `Bundle.Pullback.exists_contMDiff_hom_map_I_eq_cast` constructs a jointly smooth
complex-linear Hom field equal to the identity casts on any closed coincidence set of two
base maps. `Bundle.Pullback.contMDiff_fiberwise_comp_of_hom` gives its smooth total-space map
after smooth base change.

The native Hom section between two pullbacks by the same map is `Cⁿ` at a point exactly when its
original Hom field along that map is `Cⁿ` there, provided the map is `Cⁿ` at that point
(`Bundle.Pullback.contMDiffAt_hom_section_iff`, with the global form
`Bundle.Pullback.contMDiff_hom_section_iff`). This dictionary requires neither finite rank nor a
smooth bundle structure on the fibres.

For a field of fibrewise linear maps `A x : V (f x) → W (g x)` along two different maps, a `Cⁿ`
induced map `p ↦ (g p.proj, A p.proj p.snd)` from the total space of `f *ᵖ V` to that of `W`
gives `Cⁿ` coordinates `inCoordinates F V G W (f x₀) (f x) (g x₀) (g x) (A x)`, when the model
fibre of `V` is finite-dimensional (`Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt`).
For tangent bundles these are the tangent coordinates `inTangentCoordinates` in which prescribed
ambient differentials along an embedding are stated.

The pullback of a `C^n` vector bundle along a `C^n` map `f`, given as an element of any
`ContinuousMapClass` rather than as a bundled `C^n` map, is a `C^n` vector bundle
(`Bundle.Pullback.contMDiffVectorBundle`). In particular this makes the pullback along the
underlying continuous map `(g : C(B', B))` of a bundled `C^n` map `g` a `C^n` vector bundle
(`ContMDiffVectorBundle.pullbackContinuousMap`), and the restriction of a `C^n` vector bundle to
an open subset, its pullback along the inclusion, a `C^n` vector bundle
(`Bundle.Pullback.contMDiffVectorBundle_opens`).

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
  [FiberBundle F E] [FunLike K B' B] [ContinuousMapClass K B' B] {m n : WithTop ℕ∞}

/-- A map into a pullback bundle is `C^n` within a set at a point exactly when its base
projection and its lift to the original total space are `C^n` within that set there. -/
theorem contMDiffWithinAt_iff (f : K) {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} {s : Set X}
    {x : X} (hf : ContMDiffAt I' I n f (q x).proj) :
    ContMDiffWithinAt IX (I'.prod 𝓘(𝕜, F)) n q s x ↔
      ContMDiffWithinAt IX I' n (fun y => (q y).proj) s x ∧
        ContMDiffWithinAt IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) s x := by
  simp only [Bundle.contMDiffWithinAt_totalSpace_iff, trivializationAt,
    FiberBundle.pullback_trivializationAt', Trivialization.pullback_apply, Pullback.lift_proj]
  exact ⟨fun ⟨hq, hcoord⟩ => ⟨hq, hf.comp_contMDiffWithinAt x hq, hcoord⟩,
    fun ⟨hq, _, hcoord⟩ => ⟨hq, hcoord⟩⟩

/-- A map into a pullback bundle is `C^n` at a point exactly when its base projection and its
lift to the original total space are `C^n` there. -/
theorem contMDiffAt_iff (f : K) {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} {x : X}
    (hf : ContMDiffAt I' I n f (q x).proj) :
    ContMDiffAt IX (I'.prod 𝓘(𝕜, F)) n q x ↔
      ContMDiffAt IX I' n (fun y => (q y).proj) x ∧
        ContMDiffAt IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) x :=
  contMDiffWithinAt_iff f hf

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
      fun p : TotalSpace F E ↦ TotalSpace.mk' F' p.proj (φ p.proj p.snd))
    (f : K) (hf : ContMDiff I' I n f) :
    ContMDiff (I'.prod 𝓘(𝕜, F)) (I'.prod 𝓘(𝕜, F')) n
      fun p : TotalSpace F ((f : B' → B) *ᵖ E) ↦
        TotalSpace.mk' F' (E := (f : B' → B) *ᵖ E') p.proj (φ (f p.proj) p.snd) :=
  (contMDiff_iff f hf).2 ⟨contMDiff_proj _, hφ.comp (contMDiff_lift f hf)⟩

variable (E) in
/-- The pullback of a bundle along the identity is the bundle itself: the canonical map
`Pullback.lift` is a `C^n` diffeomorphism of total spaces, the identity on every fibre. Over a
complex model at `n = ∞` this is a biholomorphism of total spaces. -/
def idDiffeomorph :
    TotalSpace F ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E) ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯
      TotalSpace F E where
  toFun := Pullback.lift ContMDiffMap.id
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_lift _ contMDiff_id
  contMDiff_invFun := (contMDiff_iff _ contMDiff_id).2 ⟨contMDiff_proj E, contMDiff_id⟩

@[simp]
theorem idDiffeomorph_apply
    (p : TotalSpace F ((ContMDiffMap.id : C^m⟮I, B; I, B⟯) *ᵖ E)) :
    idDiffeomorph (I := I) (n := n) E p = ⟨p.proj, p.snd⟩ :=
  (rfl)

@[simp]
theorem idDiffeomorph_symm_apply (p : TotalSpace F E) :
    (idDiffeomorph (I := I) (m := m) (n := n) E).symm p = ⟨p.proj, p.snd⟩ :=
  (rfl)

variable {EM'' H'' B'' : Type*} [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM'']
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 EM'' H''}
  [TopologicalSpace B''] [ChartedSpace H'' B'']

variable (E) in
/-- Pulling back along a composite is pulling back in two steps: for `C^m` maps
`f : B'' → B'` and `g : B' → B`, the total spaces of `(g ∘ f) *ᵖ E` and `f *ᵖ (g *ᵖ E)` are
`C^n` diffeomorphic, for any `m` and `n`, by the identity on every fibre `E (g (f x))`. -/
def compDiffeomorph (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) :
    TotalSpace F ((g.comp f : B'' → B) *ᵖ E) ≃ₘ^n⟮I''.prod 𝓘(𝕜, F), I''.prod 𝓘(𝕜, F)⟯
      TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E)) where
  toFun p := ⟨p.proj, p.snd⟩
  invFun p := ⟨p.proj, p.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  -- Both total spaces are charted at `p` by the trivialization of `E` at `g (f p.proj)`, so in
  -- these coordinates the map is the identity, whatever the regularity of `f` and `g`.
  contMDiff_toFun p := contMDiffAt_totalSpace_iff.2
    ⟨contMDiffAt_proj _, (contMDiffAt_totalSpace_iff.1 (contMDiffAt_id (x := p))).2⟩
  contMDiff_invFun p := contMDiffAt_totalSpace_iff.2
    ⟨contMDiffAt_proj _, (contMDiffAt_totalSpace_iff.1 (contMDiffAt_id (x := p))).2⟩

@[simp]
theorem compDiffeomorph_apply (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯)
    (p : TotalSpace F ((g.comp f : B'' → B) *ᵖ E)) :
    compDiffeomorph (n := n) E g f p = ⟨p.proj, p.snd⟩ :=
  (rfl)

@[simp]
theorem compDiffeomorph_symm_apply (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯)
    (p : TotalSpace F ((f : B'' → B') *ᵖ ((g : B' → B) *ᵖ E))) :
    (compDiffeomorph (n := n) E g f).symm p = ⟨p.proj, p.snd⟩ :=
  (rfl)

/-- Under `compDiffeomorph`, the canonical map of the composite pullback is the composite of the
canonical maps of the two steps. -/
theorem lift_comp_compDiffeomorph (g : C^m⟮I', B'; I, B⟯) (f : C^m⟮I'', B''; I', B'⟯) :
    Pullback.lift (F := F) (E := E) g ∘ Pullback.lift f ∘ compDiffeomorph (n := n) E g f =
      Pullback.lift (g.comp f) :=
  (rfl)

/-- If `f` is a `C^n` local diffeomorphism at `x` and `m ≤ n`, a section `σ` of `E` is `C^m` at
`f x` exactly when its pullback `y ↦ σ (f y)`, a section of `f *ᵖ E`, is `C^m` at `x`. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_section_iff_pullback {f : K} {x : B'}
    (hf : IsLocalDiffeomorphAt I' I n f x) (hm : m ≤ n) {σ : ∀ b, E b} :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) m (fun b => TotalSpace.mk' F b (σ b)) (f x) ↔
      ContMDiffAt I' (I'.prod 𝓘(𝕜, F)) m
        (fun y => (TotalSpace.mk' F y (σ (f y)) : TotalSpace F ((f : B' → B) *ᵖ E))) x := by
  rw [Pullback.contMDiffAt_iff f (hf.contMDiffAt.of_le hm), ← hf.contMDiffAt_comp_iff hm]
  -- `Pullback.lift f` sends `⟨y, σ (f y)⟩` to `⟨f y, σ (f y)⟩` by definition; the dependent pair
  -- cannot be rewritten.
  exact (and_iff_right contMDiffAt_id).symm

/-- If `f` is a surjective `C^n` local diffeomorphism and `m ≤ n`, a section `σ` of `E` is `C^m`
exactly when its pullback `y ↦ σ (f y)`, a section of `f *ᵖ E`, is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_section_iff_pullback {f : K}
    (hf : IsLocalDiffeomorph I' I n f) (hsurj : Function.Surjective f) (hm : m ≤ n)
    {σ : ∀ b, E b} :
    ContMDiff I (I.prod 𝓘(𝕜, F)) m (fun b => TotalSpace.mk' F b (σ b)) ↔
      ContMDiff I' (I'.prod 𝓘(𝕜, F)) m
        (fun y => (TotalSpace.mk' F y (σ (f y)) : TotalSpace F ((f : B' → B) *ᵖ E))) := by
  refine ⟨fun h y => ((hf y).contMDiffAt_section_iff_pullback hm).1 (h (f y)), fun h b => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj b
  exact ((hf x).contMDiffAt_section_iff_pullback hm).2 (h x)

end Bundle.Pullback

section HomSection

variable {𝕜 B X F G K EB HB EX HX : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, AddCommGroup (W b)] [∀ b, Module 𝕜 (W b)] [∀ b, TopologicalSpace (W b)]
  [∀ b, IsTopologicalAddGroup (W b)] [∀ b, ContinuousSMul 𝕜 (W b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [FunLike K X B] [ContinuousMapClass K X B] {n : WithTop ℕ∞}

/-- A section of Hom between two pullbacks is `Cⁿ` at a point where the base map is `Cⁿ` exactly
when its field of maps along the base map is `Cⁿ` there in the original hom bundle. No rank or
smooth-bundle assumption is needed. -/
theorem Bundle.Pullback.contMDiffAt_hom_section_iff (f : K) {x : X}
    (hf : ContMDiffAt IX IB n f x) (A : ∀ x, V (f x) →L[𝕜] W (f x)) :
    ContMDiffAt IX (IX.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ W) x) x (A x)) x ↔
      ContMDiffAt IX (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
          (E := fun b ↦ V b →L[𝕜] W b) (f x) (A x)) x := by
  -- Near `x`, the hom coordinates of `A` between the pullbacks are its coordinates between the
  -- original bundles at the image points.
  have heq :
      (fun y ↦ ContinuousLinearMap.inCoordinates F ((f : X → B) *ᵖ V)
        G ((f : X → B) *ᵖ W) x y x y (A y)) =ᶠ[nhds x]
      (fun y ↦ ContinuousLinearMap.inCoordinates F V G W (f x) (f y) (f x) (f y) (A y)) := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      ((trivializationAt F V (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V (f x))),
      hf.continuousAt.preimage_mem_nhds
      ((trivializationAt G W (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt G W (f x)))] with y hyV hyW
    exact ContinuousLinearMap.inCoordinates_pullback_of_mem f f x y (A y) hyV hyW
  rw [contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  exact ⟨fun h ↦ ⟨hf, h.2.congr_of_eventuallyEq heq.symm⟩,
    fun h ↦ ⟨contMDiffAt_id, h.2.congr_of_eventuallyEq heq⟩⟩

/-- A section of Hom between two pullbacks is `Cⁿ` exactly when its field of maps along the
base map is `Cⁿ` in the original hom bundle. No rank or smooth-bundle assumption is needed. -/
theorem Bundle.Pullback.contMDiff_hom_section_iff (f : K) (hf : ContMDiff IX IB n f)
    (A : ∀ x, V (f x) →L[𝕜] W (f x)) :
    ContMDiff IX (IX.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x →L[𝕜] ((f : X → B) *ᵖ W) x) x (A x)) ↔
      ContMDiff IX (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G)
          (E := fun b ↦ V b →L[𝕜] W b) (f x) (A x)) :=
  forall_congr' fun x ↦ Bundle.Pullback.contMDiffAt_hom_section_iff f (hf x) A

end HomSection

section HomAlongMaps

variable {𝕜 B C X F G K L EB HB EC HC EX HX : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EC] [NormedSpace 𝕜 EC] [TopologicalSpace HC]
  {IC : ModelWithCorners 𝕜 EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*} {W : C → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ c, AddCommGroup (W c)] [∀ c, Module 𝕜 (W c)] [∀ c, TopologicalSpace (W c)]
  [∀ c, IsTopologicalAddGroup (W c)] [∀ c, ContinuousSMul 𝕜 (W c)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [FunLike K X B] [ContinuousMapClass K X B] [FunLike L X C] [ContinuousMapClass L X C]
  {n : WithTop ℕ∞}

/-- A field of fibrewise linear maps `A x : V (f x) → W (g x)` along two maps `f` and `g` whose
induced map `p ↦ (g p.proj, A p.proj p.snd)` from the total space of the pullback `f *ᵖ V` to
that of `W` is `Cⁿ`, and whose second base map `g` is `Cⁿ` at `x₀`, has `Cⁿ` coordinates
`inCoordinates F V G W (f x₀) (f x) (g x₀) (g x) (A x)` at `x₀`. For tangent bundles these are the
tangent coordinates `inTangentCoordinates` of `A`. -/
theorem Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt (f : K) (g : L) {x₀ : X}
    (hg : ContMDiffAt IX IC n g x₀) (A : ∀ x, V (f x) →L[𝕜] W (g x))
    (hA : ∀ v : V (f x₀), ContMDiffAt (IX.prod 𝓘(𝕜, F)) (IC.prod 𝓘(𝕜, G)) n
      (fun p : TotalSpace F ((f : X → B) *ᵖ V) ↦ TotalSpace.mk' G (g p.proj) (A p.proj p.snd))
      ⟨x₀, v⟩) :
    ContMDiffAt IX 𝓘(𝕜, F →L[𝕜] G) n
      (fun x ↦ ContinuousLinearMap.inCoordinates F V G W (f x₀) (f x) (g x₀) (g x) (A x)) x₀ := by
  -- Read `A` as a Hom section between the pullbacks `f *ᵖ V` and `g *ᵖ W` over `X`.
  let ϕ : ∀ x, ((f : X → B) *ᵖ V) x →L[𝕜] ((g : X → C) *ᵖ W) x := A
  have hsec := (TauCeti.contMDiffAt_hom_bundle_iff ϕ x₀).2 fun v ↦
    (Bundle.Pullback.contMDiffAt_iff g hg).2 ⟨contMDiffAt_proj _, hA v⟩
  rw [contMDiffAt_hom_bundle] at hsec
  refine hsec.2.congr_of_eventuallyEq ?_
  filter_upwards [(map_continuous f).continuousAt.preimage_mem_nhds
      ((trivializationAt F V (f x₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V (f x₀))),
    (map_continuous g).continuousAt.preimage_mem_nhds
      ((trivializationAt G W (g x₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt G W (g x₀)))] with y hyV hyW
  exact (ContinuousLinearMap.inCoordinates_pullback_of_mem f g x₀ y (A y) hyV hyW).symm

end HomAlongMaps

section ContMDiffVectorBundle

variable {𝕜 B B' F K EB HB EB' HB' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [FunLike K B' B] [ContinuousMapClass K B' B] {n : WithTop ℕ∞}

/-- The pullback of a `C^n` vector bundle along a `C^n` map `f` is a `C^n` vector bundle. This is
`ContMDiffVectorBundle.pullback` for `f` in any `ContinuousMapClass`, with the regularity of `f`
supplied as a hypothesis. -/
theorem Bundle.Pullback.contMDiffVectorBundle [ContMDiffVectorBundle n F E IB] {f : K}
    (hf : ContMDiff IB' IB n f) : ContMDiffVectorBundle n F ((f : B' → B) *ᵖ E) IB' :=
  ContMDiffVectorBundle.pullback F E IB' (⟨f, hf⟩ : C^n⟮IB', B'; IB, B⟯)

/-- The canonical pullback to an open subset is a `C^n` vector bundle. This instance uses
the smooth inclusion of the open submanifold and requires no completeness or dimension
assumption on the model fibre. -/
instance Bundle.Pullback.instContMDiffVectorBundleSubtypeVal
    [ContMDiffVectorBundle n F E IB] (U : TopologicalSpace.Opens B) :
    ContMDiffVectorBundle n F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, B)) *ᵖ E) IB :=
  ContMDiffVectorBundle.pullback F E IB ⟨Subtype.val, contMDiff_subtypeVal⟩

/-- The pullback of a `C^n` vector bundle along a `C^n` map `g`, taken along its underlying
continuous map `(g : C(B', B))`, is a `C^n` vector bundle. Mathlib's instance
`ContMDiffVectorBundle.pullback` does not apply here, since its base map is `g` itself rather than
its coercion through `C(B', B)`. -/
instance ContMDiffVectorBundle.pullbackContinuousMap [ContMDiffVectorBundle n F E IB]
    (g : C^n⟮IB', B'; IB, B⟯) : ContMDiffVectorBundle n F ((g : C(B', B)) *ᵖ E) IB' :=
  Bundle.Pullback.contMDiffVectorBundle (f := (g : C(B', B))) g.contMDiff

/-- The restriction of a `C^n` vector bundle to an open subset, its pullback along the inclusion,
is a `C^n` vector bundle. -/
instance Bundle.Pullback.contMDiffVectorBundle_opens [ContMDiffVectorBundle n F E IB]
    (U : TopologicalSpace.Opens B) :
    ContMDiffVectorBundle n F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, B)) *ᵖ E) IB :=
  Bundle.Pullback.contMDiffVectorBundle contMDiff_subtypeVal

end ContMDiffVectorBundle


open Set Function FiberBundle
open scoped ContDiff Topology

namespace Bundle.Pullback

noncomputable section LocalTransport
variable {EM HM M EP HP P F : Type*}
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V IM]
  (b₀ b₁ : C^∞⟮IP, P; IM, M⟯)
  (e : Trivialization F (π F V)) [e.IsLinear ℂ] [e.IsLinear ℝ] [MemTrivializationAtlas e]

local instance sourceSmoothBundle : ContMDiffVectorBundle ∞ F ((b₀ : P → M) *ᵖ V) IP :=
  ContMDiffVectorBundle.pullback F V IP b₀
local instance targetSmoothBundle : ContMDiffVectorBundle ∞ F ((b₁ : P → M) *ᵖ V) IP :=
  ContMDiffVectorBundle.pullback F V IP b₁

/-- The real-linear transport obtained by reading and reconstructing in one complex chart. -/
def localTransport (p : P) : V (b₀ p) →L[ℝ] V (b₁ p) :=
  ((e.symmL ℂ (b₁ p)).comp (e.continuousLinearMapAt ℂ (b₀ p))).restrictScalars ℝ

omit [IsManifold IM ∞ M] [IsManifold IP ∞ P]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V IM]
  [e.IsLinear ℝ] [MemTrivializationAtlas e] in
/-- Evaluation of local chart transport in the original source and target fibres. -/
theorem localTransport_apply (p : P) (v : V (b₀ p)) :
    localTransport b₀ b₁ e p v =
      e.symmL ℂ (b₁ p) (e.continuousLinearMapAt ℂ (b₀ p) v) := by rfl

omit [IsManifold IM ∞ M] [IsManifold IP ∞ P]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V IM]
  [e.IsLinear ℝ] [MemTrivializationAtlas e] in
/-- Local chart transport commutes with multiplication by `I`. -/
theorem localTransport_map_I (p : P) (v : V (b₀ p)) :
    localTransport b₀ b₁ e p (Complex.I • v) = Complex.I • localTransport b₀ b₁ e p v := by
  exact (((e.symmL ℂ (b₁ p)).comp
    (e.continuousLinearMapAt ℂ (b₀ p))).map_smul Complex.I v)

omit [IsManifold IM ∞ M] [IsManifold IP ∞ P]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V IM]
  [e.IsLinear ℝ] [MemTrivializationAtlas e] in
/-- The local transport in the original total space is chart reconstruction at the new base. -/
theorem lift_localTransport (v : TotalSpace F ((b₀ : P → M) *ᵖ V))
    (hv : b₀ v.proj ∈ e.baseSet ∧ b₁ v.proj ∈ e.baseSet) :
    Pullback.lift b₁ (TotalSpace.mk' F (E := (b₁ : P → M) *ᵖ V)
      v.proj (localTransport b₀ b₁ e v.proj v.snd)) =
    e.toOpenPartialHomeomorph.symm (b₁ v.proj, (e (Pullback.lift b₀ v)).2) := by
  -- The pullback total-space constructor and its projection are retyped in the original
  -- fibres, so the explicit transport and chart evaluation laws apply without inferred
  -- pullback-family instances. This reduction changes no vector or base point.
  let u : V (b₀ v.proj) := v.snd
  change (TotalSpace.mk' F (E := V) (b₁ v.proj)
    (localTransport b₀ b₁ e v.proj u)) =
      e.toOpenPartialHomeomorph.symm (b₁ v.proj, (e ⟨b₀ v.proj, u⟩).2)
  rw [localTransport_apply, e.continuousLinearMapAt_apply_of_mem ℂ hv.1, e.symmL_apply hv.2]
  exact e.mk_symm hv.2 _

omit [IsManifold IM ∞ M] [IsManifold IP ∞ P]
  [IsScalarTower ℝ ℂ F] [VectorBundle ℂ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [e.IsLinear ℝ] in
/-- Local chart transport is smooth wherever both base maps lie in the chart. -/
theorem contMDiffOn_localTransport :
    ContMDiffOn (IP.prod 𝓘(ℝ, F)) (IP.prod 𝓘(ℝ, F)) ∞
      (fun v : TotalSpace F ((b₀ : P → M) *ᵖ V) ↦
        TotalSpace.mk' F (E := (b₁ : P → M) *ᵖ V)
          v.proj (localTransport b₀ b₁ e v.proj v.snd))
      {v | b₀ v.proj ∈ e.baseSet ∧ b₁ v.proj ∈ e.baseSet} := by
  intro v hv
  have hp : ContMDiffAt (IP.prod 𝓘(ℝ, F)) IP ∞
      (fun v : TotalSpace F ((b₀ : P → M) *ᵖ V) ↦ v.proj) v := contMDiffAt_proj _
  have hl := (Pullback.contMDiff_lift b₀ b₀.contMDiff).contMDiffAt (x := v)
  have hcoord := (e.contMDiffAt (e.mem_source.mpr hv.1)).comp v hl
  have hpair := ((b₁.contMDiff.contMDiffAt).comp v hp).prodMk hcoord.snd
  have hs := (e.contMDiffAt_symm (e.mem_target.mpr hv.2)).comp v hpair
  have hU : IsOpen {v : TotalSpace F ((b₀ : P → M) *ᵖ V) |
      b₀ v.proj ∈ e.baseSet ∧ b₁ v.proj ∈ e.baseSet} :=
    (e.open_baseSet.preimage (b₀.contMDiff.continuous.comp (continuous_proj _ _))).inter
      (e.open_baseSet.preimage (b₁.contMDiff.continuous.comp (continuous_proj _ _)))
  have heq : (fun v : TotalSpace F ((b₀ : P → M) *ᵖ V) ↦
      Pullback.lift b₁ (TotalSpace.mk' F (E := (b₁ : P → M) *ᵖ V)
        v.proj (localTransport b₀ b₁ e v.proj v.snd))) =ᶠ[𝓝 v]
      (fun v ↦ e.toOpenPartialHomeomorph.symm (b₁ v.proj, (e (Pullback.lift b₀ v)).2)) := by
    filter_upwards [hU.mem_nhds hv] with w hw
    exact lift_localTransport b₀ b₁ e w hw
  apply ContMDiffAt.contMDiffWithinAt
  exact (Pullback.contMDiffAt_iff b₁ (b₁.contMDiff.contMDiffAt)).2
    ⟨hp, hs.congr_of_eventuallyEq heq⟩


omit [IsManifold IM ∞ M] [IsManifold IP ∞ P]
  [IsScalarTower ℝ ℂ F] [VectorBundle ℂ F V]
  [∀ x, ContinuousSMul ℂ (V x)] [e.IsLinear ℝ] in
/-- Local chart transport is smooth wherever both base maps lie in the chart. -/
theorem contMDiffOn_localTransport_hom [FiniteDimensional ℝ F] :
    ContMDiffOn IP (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun p ↦ ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p)
        p (localTransport b₀ b₁ e p))
      {p | b₀ p ∈ e.baseSet ∧ b₁ p ∈ e.baseSet} := by
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  apply (TauCeti.contMDiffAt_hom_bundle_iff
    (F₁ := F) (F₂ := F) (IB := IP)
    (E₁ := (b₀ : P → M) *ᵖ V) (E₂ := (b₁ : P → M) *ᵖ V)
    (localTransport b₀ b₁ e) p).2
  intro v
  have hU : IsOpen {v : TotalSpace F ((b₀ : P → M) *ᵖ V) |
      b₀ v.proj ∈ e.baseSet ∧ b₁ v.proj ∈ e.baseSet} :=
    (e.open_baseSet.preimage (b₀.contMDiff.continuous.comp (continuous_proj _ _))).inter
      (e.open_baseSet.preimage (b₁.contMDiff.continuous.comp (continuous_proj _ _)))
  exact (contMDiffOn_localTransport b₀ b₁ e ⟨p, v⟩ hp).contMDiffAt (hU.mem_nhds hp)


omit [IsManifold IM ∞ M] [IsScalarTower ℝ ℂ F]
  [∀ x, ContinuousSMul ℂ (V x)] in
/-- A smooth complex-linear Hom field extending the identity casts on a closed coincidence set. -/
theorem exists_contMDiff_hom_map_I_eq_cast [FiniteDimensional ℝ EP]
    [FiniteDimensional ℝ F] [T2Space P] [SigmaCompactSpace P]
    (D : Set P) (hD : IsClosed D) (hbase : ∀ p ∈ D, b₀ p = b₁ p) :
    ∃ A : ∀ p, ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p,
      ContMDiff IP (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p ↦ TotalSpace.mk' (F →L[ℝ] F) p (A p)) ∧
      (∀ p v, A p (Complex.I • v) = Complex.I • A p v) ∧
      ∀ p ∈ D, ∀ h : b₀ p = b₁ p, ∀ v, A p v = cast (congrArg V h) v := by
  let Z (p : P) := ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p
  let t (p : P) : Set (Z p) := {A | (∀ v, A (Complex.I • v) = Complex.I • A v) ∧
    (p ∈ D → ∀ h : b₀ p = b₁ p, ∀ v, A v = cast (congrArg V h) v)}
  have hconv (p : P) : Convex ℝ (t p) := by
    rintro A ⟨hAI, hAD⟩ B ⟨hBI, hBD⟩ a b _ _ hab
    refine ⟨fun v ↦ ?_, fun hp h v ↦ ?_⟩
    · simp only [add_apply, smul_apply, hAI, hBI,
        smul_add]
      exact congrArg₂ (· + ·) (smul_comm _ _ _) (smul_comm _ _ _)
    · simp only [add_apply, smul_apply,
        hAD hp h, hBD hp h]
      have hs (w : V (b₁ p)) : a • w + b • w = w := by
        rw [← add_smul, hab, one_smul]
      exact hs _
  have hloc (p : P) : ∃ U ∈ 𝓝 p, ∃ a : ∀ p, Z p,
      ContMDiffOn IP (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p ↦ TotalSpace.mk' (F →L[ℝ] F) p (a p)) U ∧ ∀ q ∈ U, a q ∈ t q := by
    by_cases hp : p ∈ D
    · let e := trivializationAt F V (b₀ p)
      let U := {q | b₀ q ∈ e.baseSet ∧ b₁ q ∈ e.baseSet}
      have hU : IsOpen U :=
        (e.open_baseSet.preimage b₀.contMDiff.continuous).inter
          (e.open_baseSet.preimage b₁.contMDiff.continuous)
      have hpU : p ∈ U := by
        refine ⟨mem_baseSet_trivializationAt F V (b₀ p), ?_⟩
        rw [← hbase p hp]
        exact mem_baseSet_trivializationAt F V (b₀ p)
      refine ⟨U, hU.mem_nhds hpU, localTransport b₀ b₁ e,
        contMDiffOn_localTransport_hom b₀ b₁ e, ?_⟩
      intro q hq
      refine ⟨localTransport_map_I b₀ b₁ e q, fun _ h v ↦ ?_⟩
      exact e.symmL_continuousLinearMapAt_eq_cast ℂ h hq.1 v
    · refine ⟨Dᶜ, hD.isOpen_compl.mem_nhds hp, fun _ ↦ 0, ?_, ?_⟩
      · exact (contMDiff_zeroSection (F := F →L[ℝ] F) (E := Z) (IB := IP) (n := ∞) ℝ).contMDiffOn
      · intro q hq
        exact ⟨fun v ↦ by simp, fun hqD ↦ (hq hqD).elim⟩
  obtain ⟨A, hA⟩ := exists_contMDiffSection_forall_mem_convex_of_local IP Z t hconv hloc
  exact ⟨A, A.contMDiff, fun p ↦ (hA p).1, fun p hp ↦ (hA p).2 hp⟩

omit [IsManifold IM ∞ M] [IsManifold IP ∞ P] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)] [VectorBundle ℂ F V]
  [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V IM]
  [∀ x, Module ℂ (V x)] in
/-- A smooth native Hom field induces a smooth fibrewise map after any smooth base change. -/
theorem contMDiff_fiberwise_comp_of_hom [FiniteDimensional ℝ F]
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
    [TopologicalSpace Q] [ChartedSpace HQ Q]
    (A : ∀ p, ((b₀ : P → M) *ᵖ V) p →L[ℝ] ((b₁ : P → M) *ᵖ V) p)
    (hA : ContMDiff IP (IP.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p ↦ TotalSpace.mk' (F →L[ℝ] F) p (A p))) (j : C^∞⟮IQ, Q; IP, P⟯) :
    ContMDiff (IQ.prod 𝓘(ℝ, F)) (IQ.prod 𝓘(ℝ, F)) ∞
      (fun v : TotalSpace F ((b₀.comp j : Q → M) *ᵖ V) ↦
        TotalSpace.mk' F (E := (b₁.comp j : Q → M) *ᵖ V) v.proj (A (j v.proj) v.snd)) := by
  have hAt := (TauCeti.contMDiff_hom_bundle_iff
    (IB := IP) (F₁ := F) (F₂ := F)
    (E₁ := (b₀ : P → M) *ᵖ V) (E₂ := (b₁ : P → M) *ᵖ V) A).1 hA
  have hit := Pullback.contMDiff_fiberwise
    (F := F) (F' := F) (E := (b₀ : P → M) *ᵖ V) (E' := (b₁ : P → M) *ᵖ V)
    (fun p v ↦ A p v) hAt j j.contMDiff
  have hr := (Pullback.compDiffeomorph (n := ∞) V b₁ j).symm.contMDiff.comp
    (hit.comp (Pullback.compDiffeomorph (n := ∞) V b₀ j).contMDiff)
  apply hr.congr
  intro v
  simp only [Function.comp_apply]
  rw [Pullback.compDiffeomorph_apply (n := ∞) (E := V) b₀ j v,
    Pullback.compDiffeomorph_symm_apply]


end LocalTransport

end Bundle.Pullback
