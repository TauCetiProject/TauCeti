/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BaseVertex
public import TauCeti.GroupTheory.GraphOfGroups.Hom
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree

/-!
# Functoriality of the fundamental group of a graph of groups at a vertex

A morphism `Φ : 𝔸 → 𝔹` of graphs of groups, with graph morphism `[·]`, vertex group homomorphisms
`φ_v` and twisting elements `δ_e`, sends an `𝔸`-path to a `𝔹`-path letter by letter: an element
`g ∈ A_v` is sent to the letter `φ_v g ∈ B_[v]`, and a dart `e` to the three letters
`δ_e, [e], δ_{rev e}⁻¹`. Merging consecutive vertex group letters, this is the path `μ(p)` that
Kapovich, Weidmann and Myasnikov attach to an `𝔸`-graph, for which `δ_e = e_α` and
`δ_{rev e}⁻¹ = e_ω`. The path map is compatible with concatenation and reversal and sends homotopic
paths to homotopic paths, so it induces a homomorphism `π₁.map Φ a : π₁(𝔸, a) →* π₁(𝔹, [a])`.

The identity morphism induces the identity and composite morphisms induce composite
homomorphisms. The induced homomorphisms commute with the conjugations `π₁.vertexHom` of vertex
groups and with change of base vertex. Reading paths in the presented groups, they are compatible
with the homomorphisms `π₁Tree.map Φ : π₁(𝔸, T) →* π₁(𝔹, T')` relative to sets of darts; in
particular, for spanning trees `T` and `T'` whose darts satisfy the hypothesis of `π₁Tree.map`,
`π₁.map Φ` and `π₁Tree.map Φ` correspond under the isomorphisms `π₁Equiv`.

## Main definitions

* `TauCeti.GraphOfGroups.Hom.mapLetter`, `TauCeti.GraphOfGroups.Hom.mapPath`: the `𝔹`-path read
  along a letter and along an `𝔸`-path.
* `TauCeti.GraphOfGroups.π₁.map`: the homomorphism `π₁(𝔸, a) →* π₁(𝔹, [a])` induced by a
  morphism.

## Main results

* `TauCeti.GraphOfGroups.Hom.mapPath_comp`, `TauCeti.GraphOfGroups.Hom.mapPath_reverse`: the path
  map preserves concatenation and reversal.
* `TauCeti.GraphOfGroups.Hom.edgePath_mapPath`: the underlying edge path of the image is the image
  of the underlying edge path under the graph morphism.
* `TauCeti.GraphOfGroups.Path.Homotopic.mapPath`: the path map preserves homotopy.
* `TauCeti.GraphOfGroups.π₁.map_id`, `TauCeti.GraphOfGroups.π₁.map_comp_map`: functoriality.
* `TauCeti.GraphOfGroups.π₁.map_vertexHom`: the induced homomorphism sends `p g p⁻¹` to
  `μ(p) φ(g) μ(p)⁻¹`.
* `TauCeti.GraphOfGroups.π₁.map_mulEquivOfPath`: naturality of the change of base vertex.
* `TauCeti.GraphOfGroups.π₁.toπ₁Tree_map`, `TauCeti.GraphOfGroups.π₁Equiv_map`,
  `TauCeti.GraphOfGroups.π₁.map_π₁Equiv_symm`: compatibility with the induced homomorphisms of the
  presented groups.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definitions 2.2–2.3; §3, Definition 3.1,
  Convention 3.5 and Proposition 3.7.
* H. Bass, *Covering theory for graphs of groups*, J. Pure Appl. Algebra 89 (1993), §2.
-/

public section

universe u₁ v₁ w₁ x₁ u₂ v₂ w₂ x₂ u₃ v₃ w₃ x₃

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u₁, v₁}} {Δ : SerreGraph.{u₂, v₂}} {Θ : SerreGraph.{u₃, v₃}}
  {𝔸 : GraphOfGroups.{u₁, v₁, w₁, x₁} Γ} {𝔹 : GraphOfGroups.{u₂, v₂, w₂, x₂} Δ}
  {ℂ : GraphOfGroups.{u₃, v₃, w₃, x₃} Θ}

namespace Hom

variable (Φ : Hom 𝔸 𝔹)

/-- The `𝔹`-path read along a letter of an `𝔸`-path: an element `g ∈ A_v` is read as the letter
`φ_v g`, and a dart `e` as the letters `δ_e, [e], δ_{rev e}⁻¹`. -/
def mapLetter : ∀ {x y : 𝔸.LetterVertex}, 𝔸.Letter x y →
    𝔹.Path ⟨Φ.graph.mapV x.as⟩ ⟨Φ.graph.mapV y.as⟩
  | _, _, .vertex g => Path.ofVertex (Φ.vertexHom _ g)
  | _, _, .dart f => ((Path.ofVertex (Φ.twistArrow f)).cons (.dart (Φ.graph.mapArrow f))).cons
      (.vertex (Φ.twistArrow (Quiver.reverse f))⁻¹)

@[simp] theorem mapLetter_vertex {a : Γ.V} (g : 𝔸.vertexGroup a) :
    Φ.mapLetter (Letter.vertex g) = Path.ofVertex (Φ.vertexHom a g) := (rfl)

@[simp] theorem mapLetter_dart {a b : Γ.V} (f : a ⟶ b) :
    Φ.mapLetter (Letter.dart (𝔸 := 𝔸) f) =
      ((Path.ofVertex (Φ.twistArrow f)).cons (Letter.dart (Φ.graph.mapArrow f))).cons
        (Letter.vertex (Φ.twistArrow (Quiver.reverse f))⁻¹) := (rfl)

/-- Reading the reverse of a letter gives the reverse path. -/
@[simp] theorem mapLetter_reverse {x y : 𝔸.LetterVertex} (l : 𝔸.Letter x y) :
    Φ.mapLetter (Quiver.reverse (V := 𝔸.LetterVertex) l) = (Φ.mapLetter l).reverse := by
  cases l with
  | vertex g => simp
  | dart f => simp [Path.ofVertex_eq_nil_cons, Quiver.Path.reverse, Quiver.Hom.toPath]

/-- The path map of a morphism: the `𝔹`-path read along an `𝔸`-path, letter by letter. -/
def mapPath {x : 𝔸.LetterVertex} : ∀ {y : 𝔸.LetterVertex}, 𝔸.Path x y →
    𝔹.Path ⟨Φ.graph.mapV x.as⟩ ⟨Φ.graph.mapV y.as⟩
  | _, .nil => .nil
  | _, .cons p l => (mapPath p).comp (Φ.mapLetter l)

section mapPath

variable {x y z : 𝔸.LetterVertex}

@[simp] theorem mapPath_nil : Φ.mapPath (Quiver.Path.nil : 𝔸.Path x x) = .nil := (rfl)

@[simp] theorem mapPath_cons (p : 𝔸.Path x y) (l : 𝔸.Letter y z) :
    Φ.mapPath (p.cons l) = (Φ.mapPath p).comp (Φ.mapLetter l) := (rfl)

@[simp] theorem mapPath_comp (p : 𝔸.Path x y) (q : 𝔸.Path y z) :
    Φ.mapPath (p.comp q) = (Φ.mapPath p).comp (Φ.mapPath q) := by
  induction q with
  | nil => rfl
  | cons q l ih => simp [ih, Quiver.Path.comp_assoc]

@[simp] theorem mapPath_toPath (l : 𝔸.Letter x y) :
    Φ.mapPath (Quiver.Hom.toPath (V := 𝔸.LetterVertex) l) = Φ.mapLetter l := by
  rw [Quiver.Hom.toPath, mapPath_cons, mapPath_nil, Quiver.Path.nil_comp]

@[simp] theorem mapPath_ofVertex {a : Γ.V} (g : 𝔸.vertexGroup a) :
    Φ.mapPath (Path.ofVertex g) = Path.ofVertex (Φ.vertexHom a g) := by
  rw [Path.ofVertex_def, mapPath_toPath, mapLetter_vertex]

@[simp] theorem mapPath_ofDart {a b : Γ.V} (f : a ⟶ b) :
    Φ.mapPath (Path.ofDart (𝔸 := 𝔸) f) =
      ((Path.ofVertex (Φ.twistArrow f)).cons (Letter.dart (Φ.graph.mapArrow f))).cons
        (Letter.vertex (Φ.twistArrow (Quiver.reverse f))⁻¹) := by
  rw [Path.ofDart_def, mapPath_toPath, mapLetter_dart]

/-- The path map commutes with reversal. -/
@[simp] theorem mapPath_reverse (p : 𝔸.Path x y) : Φ.mapPath p.reverse = (Φ.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p l ih =>
    rw [Quiver.Path.reverse, mapPath_comp, ih, mapPath_cons, Quiver.Path.reverse_comp,
      mapPath_toPath, mapLetter_reverse]

/-- The image of a path followed by an element `g ∈ A_a`: the image of the path followed by the
letter `φ_a g`. -/
private theorem mapPath_cons_vertex {a : Γ.V} (p : 𝔸.Path x ⟨a⟩) (g : 𝔸.vertexGroup a) :
    Φ.mapPath (p.cons (Letter.vertex g)) = (Φ.mapPath p).cons (Letter.vertex (Φ.vertexHom a g)) :=
  Path.comp_ofVertex ..

/-- The image of a path followed by a dart `f`: the image of the path followed by the letters
`δ_f, [f], δ_{rev f}⁻¹`. -/
private theorem mapPath_cons_dart {a b : Γ.V} (p : 𝔸.Path x ⟨a⟩) (f : a ⟶ b) :
    Φ.mapPath (p.cons (Letter.dart f)) =
      (((Φ.mapPath p).cons (Letter.vertex (Φ.twistArrow f))).cons
        (Letter.dart (Φ.graph.mapArrow f))).cons
        (Letter.vertex (Φ.twistArrow (Quiver.reverse f))⁻¹) := by
  rw [mapPath_cons, mapLetter_dart, Quiver.Path.comp_cons, Quiver.Path.comp_cons,
    Path.comp_ofVertex]

/-- The underlying edge path of the image of an `𝔸`-path is the image of its underlying edge
path under the graph morphism. -/
@[simp] theorem edgePath_mapPath (p : 𝔸.Path x y) :
    (Φ.mapPath p).edgePath = Φ.graph.toPrefunctor.mapPath p.edgePath := by
  induction p with
  | nil => simp
  | cons p l ih =>
    cases l with
    | vertex g => rwa [mapPath_cons_vertex, Path.edgePath_cons_vertex, Path.edgePath_cons_vertex]
    | dart f =>
      rw [mapPath_cons_dart, Path.edgePath_cons_vertex, Path.edgePath_cons_dart,
        Path.edgePath_cons_vertex, ih, Path.edgePath_cons_dart, Prefunctor.mapPath_cons,
        SerreGraph.Hom.toPrefunctor_map]
      -- The two sides differ only in the implicit endpoints of `cons`: `mapV` on the left and
      -- `toPrefunctor.obj` on the right, which agree by unfolding `SerreGraph.Hom.toPrefunctor`.
      rfl

end mapPath

end Hom

namespace Path.Homotopic

variable {x y : 𝔸.LetterVertex}

/-- Moving an edge group element across a dart flanked by vertex group letters:
`d, e, d'⁻¹, d' ω_e(c) d'⁻¹ ~ d α_e(c) d⁻¹, d, e, d'⁻¹`. -/
private theorem cons_dart_ωArrow_conj {z : 𝔹.LetterVertex} {a b : Δ.V} (r : 𝔹.Path z ⟨a⟩)
    (d : 𝔹.vertexGroup a) (d' : 𝔹.vertexGroup b) (e : a ⟶ b) (c : 𝔹.edgeGroup (Δ.toGeomEdge e.1)) :
    Homotopic ((((r.cons (Letter.vertex d)).cons (Letter.dart e)).cons (Letter.vertex d'⁻¹)).cons
        (Letter.vertex (d' * 𝔹.ωArrow e c * d'⁻¹)))
      ((((r.cons (Letter.vertex (d * 𝔹.αArrow e c * d⁻¹))).cons (Letter.vertex d)).cons
        (Letter.dart e)).cons (Letter.vertex d'⁻¹)) := by
  -- Both sides are homotopic to `d, α_e(c), e, d'⁻¹`.
  have h₁ : Homotopic ((((r.cons (Letter.vertex d)).cons (Letter.dart e)).cons
      (Letter.vertex d'⁻¹)).cons (Letter.vertex (d' * 𝔹.ωArrow e c * d'⁻¹)))
      ((((r.cons (Letter.vertex d)).cons (Letter.vertex (𝔹.αArrow e c))).cons
        (Letter.dart e)).cons (Letter.vertex d'⁻¹)) := by
    refine (Homotopic.mul _ _ _).trans ?_
    rw [show d'⁻¹ * (d' * 𝔹.ωArrow e c * d'⁻¹) = 𝔹.ωArrow e c * d'⁻¹ by group]
    exact (Homotopic.mul _ _ _).symm.trans ((Homotopic.dart_ωArrow _ e c).cons _)
  refine h₁.trans (((((Homotopic.mul _ _ _).cons _).cons _).trans ?_).symm)
  rw [show d * 𝔹.αArrow e c * d⁻¹ * d = d * 𝔹.αArrow e c by group]
  exact (((Homotopic.mul _ _ _).symm.cons _).cons _)

/-- The path map respects the elementary move `e, ω_e(c) ~ α_e(c), e`. -/
private theorem mapPath_dart_ω (Φ : Hom 𝔸 𝔹) (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e))
    (p : 𝔸.Path x ⟨Γ.src e⟩) :
    (Φ.mapPath ((p.cons (Letter.dart (Γ.dart e))).cons (Letter.vertex (𝔸.ω e c)))).Homotopic
      (Φ.mapPath ((p.cons (Letter.vertex (𝔸.α e c))).cons (Letter.dart (Γ.dart e)))) := by
  -- By the compatibility of `Φ` with `α` and `ω`, both images are homotopic to
  -- `δ_e, α_[e](φ_e c), [e], δ_{rev e}⁻¹`.
  rw [Hom.mapPath_cons_vertex, Hom.mapPath_cons_dart, Hom.mapPath_cons_dart,
    Hom.mapPath_cons_vertex, Φ.vertexHom_ω, Φ.vertexHom_α, Hom.twistArrow_dart,
    Hom.twistArrow_reverse_dart, Γ.dart_def]
  -- The image dart `[e]`, as an arrow between the images of the endpoints of `e`.
  let E : Φ.graph.mapV (Γ.src e) ⟶ Φ.graph.mapV (Γ.tgt e) := Φ.graph.mapArrow ⟨e, rfl, rfl⟩
  have hα : 𝔹.αArrow E (Φ.edgeHom e c) = MulEquiv.cast (M := 𝔹.vertexGroup)
      (Φ.graph.map_src e) (𝔹.α (Φ.graph.mapE e) (Φ.edgeHom e c)) := αArrow_apply ..
  have hω : 𝔹.ωArrow E (Φ.edgeHom e c) = MulEquiv.cast (M := 𝔹.vertexGroup)
      (Φ.graph.map_tgt _ e) (𝔹.ω (Φ.graph.mapE e) (Φ.edgeHom e c)) := ωArrow_apply ..
  rw [← hα, ← hω]
  exact cons_dart_ωArrow_conj (Φ.mapPath p) _ _ E _

/-- The path map of a morphism of graphs of groups sends homotopic `𝔸`-paths to homotopic
`𝔹`-paths. -/
theorem mapPath (Φ : Hom 𝔸 𝔹) {p q : 𝔸.Path x y} (h : p.Homotopic q) :
    (Φ.mapPath p).Homotopic (Φ.mapPath q) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cons _ l ih =>
    rw [Hom.mapPath_cons, Hom.mapPath_cons]
    exact ih.comp_right _
  | mul p g h =>
    rw [Hom.mapPath_cons_vertex, Hom.mapPath_cons_vertex, Hom.mapPath_cons_vertex, map_mul]
    exact .mul _ _ _
  | one p =>
    rw [Hom.mapPath_cons_vertex, map_one]
    exact .one _
  | dart_reverse p e =>
    rw [Hom.mapPath_cons, Hom.mapPath_cons, ← Letter.reverse_dart, Hom.mapLetter_reverse,
      Quiver.Path.comp_assoc]
    simpa using (comp_reverse (Φ.mapLetter (Letter.dart e))).comp_left (Φ.mapPath p)
  | dart_ω e c p => exact mapPath_dart_ω Φ e c p

/-- The path map of the identity morphism is homotopic to the identity. -/
theorem id_mapPath (p : 𝔸.Path x y) : ((Hom.id 𝔸).mapPath p).Homotopic p := by
  induction p with
  | nil => exact .refl _
  | cons p l ih =>
    cases l with
    | vertex g =>
      rw [Hom.mapPath_cons_vertex]
      exact ih.cons _
    | dart f =>
      rw [Hom.mapPath_cons_dart, Hom.id_twistArrow, Hom.id_twistArrow, inv_one]
      exact (Homotopic.one _).trans (((Homotopic.one _).trans ih).cons _)

/-- Merging the twisting letters of a composite: `g₁ g₂, e, (h₁ h₂)⁻¹ ~ g₁, g₂, e, h₂⁻¹, h₁⁻¹`. -/
private theorem cons_mul_dart_mul_inv {z : 𝔹.LetterVertex} {a b : Δ.V} {r r' : 𝔹.Path z ⟨a⟩}
    (h : r.Homotopic r') (g₁ g₂ : 𝔹.vertexGroup a) (e : a ⟶ b) (h₁ h₂ : 𝔹.vertexGroup b) :
    Homotopic (((r.cons (Letter.vertex (g₁ * g₂))).cons (Letter.dart e)).cons
        (Letter.vertex (h₁ * h₂)⁻¹))
      (((((r'.cons (Letter.vertex g₁)).cons (Letter.vertex g₂)).cons (Letter.dart e)).cons
        (Letter.vertex h₂⁻¹)).cons (Letter.vertex h₁⁻¹)) := by
  refine Homotopic.symm ((Homotopic.mul _ _ _).trans ?_)
  rw [← mul_inv_rev]
  exact ((((Homotopic.mul _ _ _).trans (h.symm.cons _)).cons _).cons _)

/-- The path map of a composite morphism is homotopic to the composite of the path maps. -/
theorem comp_mapPath (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) (p : 𝔸.Path x y) :
    ((Ψ.comp Φ).mapPath p).Homotopic (Ψ.mapPath (Φ.mapPath p)) := by
  induction p with
  | nil => exact .refl _
  | cons p l ih =>
    cases l with
    | vertex g =>
      rw [Hom.mapPath_cons_vertex, Hom.mapPath_cons_vertex, Hom.mapPath_cons_vertex]
      exact ih.cons _
    | dart f =>
      rw [Hom.mapPath_cons_dart, Hom.mapPath_cons_dart Φ p f, Hom.mapPath_cons_vertex,
        Hom.mapPath_cons_dart Ψ _ (Φ.graph.mapArrow f), Hom.mapPath_cons_vertex,
        Hom.comp_twistArrow, Hom.comp_twistArrow, map_inv, SerreGraph.Hom.mapArrow_reverse]
      exact cons_mul_dart_mul_inv ih _ _ _ _ _

end Path.Homotopic

namespace π₁

variable {a b c : Γ.V}

/-- The homomorphism `π₁(𝔸, a) →* π₁(𝔹, [a])` induced by a morphism `Φ : 𝔸 → 𝔹` of graphs of
groups: the class of a closed `𝔸`-path `p` is sent to the class of its image `μ(p)`. -/
def map (Φ : Hom 𝔸 𝔹) (a : Γ.V) : π₁ 𝔸 a →* π₁ 𝔹 (Φ.graph.mapV a) where
  toFun := lift (fun p => mk (Φ.mapPath p)) fun _ _ h => mk_eq_mk_iff.2 (h.mapPath Φ)
  map_one' := by rw [← mk_nil, lift_mk, Hom.mapPath_nil, mk_nil]
  map_mul' x y := induction_on x fun p => induction_on y fun q => by
    rw [← mk_comp, lift_mk, lift_mk, lift_mk, Hom.mapPath_comp, mk_comp]

section map

variable (Φ : Hom 𝔸 𝔹)

@[simp] theorem map_mk (p : 𝔸.Path ⟨a⟩ ⟨a⟩) : map Φ a (mk p) = mk (Φ.mapPath p) := lift_mk ..

/-- The induced homomorphism sends `p g p⁻¹` to `μ(p) φ(g) μ(p)⁻¹`. -/
@[simp] theorem map_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b) :
    map Φ a (vertexHom p g) = vertexHom (Φ.mapPath p) (Φ.vertexHom b g) := by
  rw [vertexHom_apply, map_mk, Hom.mapPath_comp, Hom.mapPath_comp, Hom.mapPath_reverse,
    Hom.mapPath_ofVertex, vertexHom_apply]

/-- The induced homomorphism composed with the conjugation of `A_b` along `p` is the conjugation of
`B_[b]` along `μ(p)` composed with `φ_b`. -/
@[simp] theorem map_comp_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (map Φ a).comp (vertexHom p) = (vertexHom (Φ.mapPath p)).comp (Φ.vertexHom b) :=
  MonoidHom.ext (map_vertexHom Φ p)

/-- The induced homomorphisms commute with change of base vertex: changing the base vertex along
`p` and then applying `Φ` is applying `Φ` and then changing the base vertex along `μ(p)`. -/
theorem map_mulEquivOfPath (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (x : π₁ 𝔸 a) :
    map Φ b (mulEquivOfPath p x) = mulEquivOfPath (Φ.mapPath p) (map Φ a x) :=
  induction_on x fun q => by
    rw [mulEquivOfPath_mk, map_mk, map_mk, mulEquivOfPath_mk, Hom.mapPath_comp,
      Hom.mapPath_comp, Hom.mapPath_reverse]

end map

/-- The identity morphism induces the identity of `π₁(𝔸, a)`. -/
@[simp] theorem map_id (a : Γ.V) : map (Hom.id 𝔸) a = MonoidHom.id (π₁ 𝔸 a) :=
  MonoidHom.ext fun x => induction_on x fun p => by
    rw [map_mk, MonoidHom.id_apply, mk_eq_mk_iff]
    exact Path.Homotopic.id_mapPath p

/-- The homomorphism induced by a composite morphism is the composite of the induced
homomorphisms. -/
@[simp] theorem map_comp_map (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) (a : Γ.V) :
    (map Ψ (Φ.graph.mapV a)).comp (map Φ a) = map (Ψ.comp Φ) a :=
  MonoidHom.ext fun x => induction_on x fun p => by
    rw [MonoidHom.comp_apply, map_mk, map_mk, map_mk, mk_eq_mk_iff]
    exact (Path.Homotopic.comp_mapPath Ψ Φ p).symm

/-- The image of an element under the homomorphism induced by a composite morphism. -/
@[simp] theorem map_map (Ψ : Hom 𝔹 ℂ) (Φ : Hom 𝔸 𝔹) (a : Γ.V) (x : π₁ 𝔸 a) :
    map Ψ (Φ.graph.mapV a) (map Φ a x) = map (Ψ.comp Φ) a x :=
  DFunLike.congr_fun (map_comp_map Ψ Φ a) x

end π₁

/-! ### Compatibility with the presented groups -/

section toπ₁Tree

variable (Φ : Hom 𝔸 𝔹) {T : Set Γ.E} {T' : Set Δ.E} (hT : ∀ e ∈ T, Φ.edgeImage T' e = 1)

/-- Reading the image of a letter in `π₁(𝔹, T')` is applying `π₁Tree.map Φ` to the reading of the
letter in `π₁(𝔸, T)`. -/
theorem Path.toπ₁Tree_mapLetter {x y : 𝔸.LetterVertex} (l : 𝔸.Letter x y) :
    (Φ.mapLetter l).toπ₁Tree T' = π₁Tree.map Φ hT (l.toπ₁Tree T) := by
  cases l with
  | vertex g => simp
  | dart f =>
    rw [Hom.mapLetter_dart, Φ.twistArrow_eq_cast (Quiver.reverse f) (Γ.reverse_val f)
      (congrArg Φ.graph.mapV ((Γ.src_rev _).trans f.2.2))]
    simp [Hom.twistArrow_def, π₁Tree.of_cast, Hom.edgeImage_def, mul_assoc, -MulEquiv.cast_apply]

/-- Reading the image of an `𝔸`-path in `π₁(𝔹, T')` is applying `π₁Tree.map Φ` to the reading of
the path in `π₁(𝔸, T)`. -/
theorem Path.toπ₁Tree_mapPath {x y : 𝔸.LetterVertex} (p : 𝔸.Path x y) :
    (Φ.mapPath p).toπ₁Tree T' = π₁Tree.map Φ hT (p.toπ₁Tree T) := by
  induction p with
  | nil => rw [Hom.mapPath_nil, toπ₁Tree_nil, toπ₁Tree_nil, map_one]
  | cons p l ih =>
    rw [Hom.mapPath_cons, toπ₁Tree_comp, toπ₁Tree_cons, map_mul, ih, toπ₁Tree_mapLetter Φ hT]

/-- The homomorphism induced on the fundamental groups at vertices and the homomorphism induced on
the presented groups commute with the reading maps `π₁(𝔸, a) →* π₁(𝔸, T)`. -/
theorem π₁.toπ₁Tree_map (a : Γ.V) (x : π₁ 𝔸 a) :
    π₁.toπ₁Tree 𝔹 (Φ.graph.mapV a) T' (π₁.map Φ a x) = π₁Tree.map Φ hT (π₁.toπ₁Tree 𝔸 a T x) :=
  π₁.induction_on x fun p => by
    rw [π₁.map_mk, π₁.toπ₁Tree_mk, π₁.toπ₁Tree_mk, Path.toπ₁Tree_mapPath Φ hT]

end toπ₁Tree

section π₁Equiv

variable (Φ : Hom 𝔸 𝔹) {v₀ : Γ.V} {T : Γ.SpanningTree} {T' : Δ.SpanningTree}
  (hT : ∀ e ∈ T.darts, Φ.edgeImage T'.darts e = 1)

/-- For spanning trees `T` and `T'` whose darts satisfy the hypothesis of `π₁Tree.map`, the
isomorphisms `π₁Equiv` carry `π₁.map Φ` to `π₁Tree.map Φ`. -/
theorem π₁Equiv_map (x : π₁ 𝔸 v₀) :
    π₁Equiv 𝔹 (Φ.graph.mapV v₀) T' (π₁.map Φ v₀ x) = π₁Tree.map Φ hT (π₁Equiv 𝔸 v₀ T x) := by
  rw [π₁Equiv_apply, π₁Equiv_apply, π₁.toπ₁Tree_map Φ hT]

variable (v₀) in
/-- The homomorphism `π₁.map Φ`, read through the isomorphisms `π₁Equiv`, is `π₁Tree.map Φ`. -/
theorem π₁.map_π₁Equiv_symm (y : π₁Tree 𝔸 T.darts) : π₁.map Φ v₀ ((π₁Equiv 𝔸 v₀ T).symm y) =
    (π₁Equiv 𝔹 (Φ.graph.mapV v₀) T').symm (π₁Tree.map Φ hT y) := by
  rw [MulEquiv.eq_symm_apply, π₁Equiv_map Φ hT, MulEquiv.apply_symm_apply]

end π₁Equiv

end GraphOfGroups

end TauCeti
