/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Preorder.Finite
public import TauCeti.Geometry.Toric.Algebraic.Cone
public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Finite fans of toric cones and their morphisms

A *fan* is the combinatorial datum from which a toric variety is glued: a finite family of toric
cones in one real vector space, closed under passing to faces, and such that the intersection of
any two members is a face of each of them. This file defines fans and their morphisms, computes
the elementary consequences of the axioms, and proves the functoriality of the support.

The two axioms have complementary roles. Closure under faces makes the affine charts of a fan
overlap in charts of the same family, and the intersection axiom makes those overlaps open
immersions on both sides. Together they force the zero cone into every nonempty fan, which is why
every affine chart of a fan contains the dense torus.

## Main declarations

* `TauCeti.Toric.Fan`: a finite fan of toric cones for a lattice map `i : N →+ V`.
* `TauCeti.Toric.Fan.inf_mem` and `TauCeti.Toric.Fan.bot_mem`: the intersection of two cones of a
  fan is again one, and the zero cone belongs to every nonempty fan.
* `TauCeti.Toric.Fan.support` and `TauCeti.Toric.Fan.IsComplete`: the union of the cones of a fan,
  and the condition that it fills the ambient real vector space.
* `TauCeti.Toric.Fan.ofCone`: the faces of a single toric cone form a fan, whose support is that
  cone. This is the fan of an affine toric variety.
* `TauCeti.Toric.Fan.subfan`: a subset of the cones of a fan which is closed under faces is a fan,
  and `TauCeti.Toric.Fan.ofCone_eq_subfan` identifies the subfan of the faces of a cone of a fan
  with the fan of that cone.
* `TauCeti.Toric.FanHom`: a morphism of fans, namely a map of the integral vectors, a compatible
  real-linear map, and the condition that every source cone lands in some target cone.
* `TauCeti.Toric.FanHom.realMap_eq`: the real-linear part of a fan morphism is determined by its
  integral part, so `TauCeti.Toric.FanHom.ext` needs only the latter.
* `TauCeti.Toric.FanHom.id`, `TauCeti.Toric.FanHom.comp` and the identity, unit and associativity
  laws they satisfy.
* `TauCeti.Toric.FanHom.mapsTo_support`: a fan morphism maps the support of its source into the
  support of its target.
* `TauCeti.Toric.FanHom.exists_isLeast_cone`: the target cones containing the image of a given
  source cone have a least element, so a fan morphism has a well-defined cone-by-cone description.

## Implementation notes

Closure under faces is stated with Mathlib's `PointedCone.IsFaceOf` rather than with its bundled
face lattice `PointedCone.Face`; the two are interchangeable, and the unbundled form avoids a
coercion at every use site.

Only the left half `(σ ⊓ τ).IsFaceOf σ` of the intersection axiom is a field: its right half is
the same statement with the two cones exchanged, and `TauCeti.Toric.Fan.inf_isFaceOf_right`
derives it.

A `Fan` carries the proof that its ambient lattice map is an integral lattice. This is what makes
the real-linear part of a fan morphism redundant data rather than a choice, and every later layer
of the toric construction needs it; carrying it here spares each of them a separate hypothesis.

## References

The mathematics is §1.4 of W. Fulton, *Introduction to Toric Varieties*, and §3.1 of D. Cox,
J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}

/-- A *finite fan* for the lattice map `i : N →+ V` is a finite family of toric cones in `V`,
closed under passing to faces, whose pairwise intersections are faces of both members. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
structure Fan (i : N →+ V) where
  /-- The ambient map of integral vectors is an integral lattice. -/
  lattice : IsIntegralLattice i
  /-- The cones of the fan. -/
  cones : Set (PointedCone ℝ V)
  /-- A fan has finitely many cones. -/
  finite_cones : cones.Finite
  /-- Every cone of a fan is a toric cone. -/
  isToricCone : ∀ ⦃σ⦄, σ ∈ cones → IsToricCone i σ
  /-- The cones of a fan are closed under passing to faces. -/
  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ cones → τ.IsFaceOf σ → τ ∈ cones
  /-- The intersection of two cones of a fan is a face of the first one. Exchanging the two cones
  gives the same statement for the second one, so only this half is a field. -/
  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ cones → τ ∈ cones → (σ ⊓ τ).IsFaceOf σ

namespace Fan

variable (Φ : Fan i)

/-- A fan is determined by its set of cones. -/
@[ext]
theorem ext {Φ Ψ : Fan i} (h : Φ.cones = Ψ.cones) : Φ = Ψ := by
  cases Φ with | mk _ C _ _ _ _ =>
  cases Ψ with | mk _ D _ _ _ _ =>
  obtain rfl : C = D := h
  rfl

/-- The intersection of two cones of a fan is a face of the second one. -/
theorem inf_isFaceOf_right (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    (σ ⊓ τ).IsFaceOf τ :=
  inf_comm σ τ ▸ Φ.inf_isFaceOf_left hτ hσ

/-- The intersection of two cones of a fan is again a cone of the fan: it is a face of each of
them, and the cones of a fan are closed under faces. -/
theorem inf_mem (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    σ ⊓ τ ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (Φ.inf_isFaceOf_left hσ hτ)

/-- A nonempty fan contains the zero cone. Its affine chart is the dense torus, which is therefore
an open subset of every chart of the fan. -/
theorem bot_mem (hσ : σ ∈ Φ.cones) : (⊥ : PointedCone ℝ V) ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (PointedCone.bot_isFaceOf (Φ.isToricCone hσ).salient)

/-! ### Support and completeness -/

/-- The *support* of a fan is the union of its cones. -/
def support : Set V := ⋃ σ ∈ Φ.cones, (σ : Set V)

/-- A point lies in the support of a fan exactly when some cone of the fan contains it. -/
@[simp]
theorem mem_support {x : V} : x ∈ Φ.support ↔ ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [support]

theorem subset_support (hσ : σ ∈ Φ.cones) : (σ : Set V) ⊆ Φ.support :=
  fun _ hx ↦ Φ.mem_support.2 ⟨σ, hσ, hx⟩

/-- The origin lies in the support of every nonempty fan. -/
theorem zero_mem_support (hσ : σ ∈ Φ.cones) : (0 : V) ∈ Φ.support :=
  Φ.mem_support.2 ⟨σ, hσ, zero_mem σ⟩

/-- A fan is *complete* when its cones cover the ambient real vector space. -/
def IsComplete : Prop := Φ.support = Set.univ

/-- Completeness, spelled pointwise. -/
theorem isComplete_iff : Φ.IsComplete ↔ ∀ x : V, ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [IsComplete, Set.eq_univ_iff_forall]

/-! ### The fan of a single cone -/

/-- The faces of a toric cone form a fan, the fan of the affine toric variety of that cone. -/
def ofCone (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) : Fan i where
  lattice := hi
  cones := {τ | τ.IsFaceOf σ}
  finite_cones := by
    have : Finite σ.Face := PointedCone.FG.finite_face hσ.fg
    have hrange : {τ : PointedCone ℝ V | τ.IsFaceOf σ} =
        Set.range fun F : σ.Face ↦ F.toPointedCone := by
      ext τ
      exact ⟨fun h ↦ ⟨⟨τ, h⟩, rfl⟩, fun ⟨F, hF⟩ ↦ hF ▸ F.isFaceOf⟩
    exact hrange ▸ Set.finite_range _
  isToricCone _ hτ := hσ.of_isFaceOf hτ
  mem_of_isFaceOf _ _ hτ hυ := hυ.trans hτ
  inf_isFaceOf_left _ _ hτ hυ :=
    (PointedCone.IsFaceOf.isFaceOf_iff_le (hτ.inf_left hυ) hτ).2 inf_le_left

/-- The cones of the fan of a cone are exactly the faces of that cone. -/
@[simp]
theorem mem_ofCone_cones (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    τ ∈ (ofCone hi hσ).cones ↔ τ.IsFaceOf σ := Iff.rfl

/-- The support of the fan of a cone is that cone. -/
@[simp]
theorem support_ofCone (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    (ofCone hi hσ).support = (σ : Set V) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨τ, hτ, hxτ⟩ := (ofCone hi hσ).mem_support.1 hx
    exact hτ.le hxτ
  · exact (ofCone hi hσ).subset_support (PointedCone.IsFaceOf.refl σ) hx

/-! ### Subfans -/

variable (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

/-- A subset of the cones of a fan which is itself closed under passing to faces is a fan. -/
@[expose]
def subfan : Fan i where
  lattice := Φ.lattice
  cones := S
  finite_cones := Φ.finite_cones.subset hS
  isToricCone _ hσ := Φ.isToricCone (hS hσ)
  mem_of_isFaceOf _ _ hσ hτ := hface hσ hτ
  inf_isFaceOf_left _ _ hσ hτ := Φ.inf_isFaceOf_left (hS hσ) (hS hτ)

/-- The cones of a subfan are the chosen subset. -/
@[simp]
theorem subfan_cones : (Φ.subfan S hS hface).cones = S := rfl

/-- The support of a subfan is contained in the support of the ambient fan. -/
theorem support_subfan_subset : (Φ.subfan S hS hface).support ⊆ Φ.support := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := (Φ.subfan S hS hface).mem_support.1 hx
  exact Φ.subset_support (hS hσ) hxσ

/-- The faces of a cone of a fan are again cones of the fan, so they form a subfan of it. -/
theorem isFaceOf_subset_cones (hσ : σ ∈ Φ.cones) :
    {τ : PointedCone ℝ V | τ.IsFaceOf σ} ⊆ Φ.cones :=
  fun _ hτ ↦ Φ.mem_of_isFaceOf hσ hτ

/-- The subfan of the faces of a cone of a fan is the fan of that cone. -/
theorem ofCone_eq_subfan (hσ : σ ∈ Φ.cones) :
    ofCone Φ.lattice (Φ.isToricCone hσ) =
      Φ.subfan {τ | τ.IsFaceOf σ} (Φ.isFaceOf_subset_cones hσ) fun _ _ hτ hυ ↦ hυ.trans hτ :=
  Fan.ext rfl

end Fan

/-! ### Morphisms of fans -/

/-- A *morphism of fans* is a map of the integral vectors together with the compatible real-linear
map, subject to the condition that every cone of the source lands inside some cone of the
target. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
structure FanHom (Φ : Fan i) (Ψ : Fan i') where
  /-- The underlying map of integral vectors. -/
  latticeMap : N →+ N'
  /-- The real-linear map extending `latticeMap`. -/
  realMap : V →ₗ[ℝ] V'
  /-- The two maps agree on integral vectors. -/
  map_lattice : ∀ n, realMap (i n) = i' (latticeMap n)
  /-- Every cone of the source fan is carried into a cone of the target fan. -/
  map_cone : ∀ ⦃σ⦄, σ ∈ Φ.cones → ∃ τ ∈ Ψ.cones, σ.map realMap ≤ τ

namespace FanHom

variable {Φ : Fan i} {Ψ : Fan i'}

/-- The real-linear part of a fan morphism is the scalar extension of its integral part. It is
therefore determined by the integral part rather than being an independent choice. -/
theorem realMap_eq (f : FanHom Φ Ψ) : f.realMap = Φ.lattice.extend i' f.latticeMap :=
  Φ.lattice.eq_extend f.map_lattice

/-- A fan morphism is determined by its map of integral vectors. -/
@[ext]
theorem ext {f g : FanHom Φ Ψ} (h : f.latticeMap = g.latticeMap) : f = g := by
  have hr : f.realMap = g.realMap := by rw [f.realMap_eq, g.realMap_eq, h]
  cases f with | mk fl fr _ _ =>
  cases g with | mk gl gr _ _ =>
  obtain rfl : fl = gl := h
  obtain rfl : fr = gr := hr
  rfl

/-- Build a fan morphism from a map of integral vectors alone, using that its real-linear part is
forced to be the scalar extension. -/
@[expose]
noncomputable def ofLatticeMap (Φ : Fan i) (Ψ : Fan i') (f : N →+ N')
    (hf : ∀ ⦃σ⦄, σ ∈ Φ.cones → ∃ τ ∈ Ψ.cones, σ.map (Φ.lattice.extend i' f) ≤ τ) :
    FanHom Φ Ψ where
  latticeMap := f
  realMap := Φ.lattice.extend i' f
  map_lattice n := Φ.lattice.extend_apply i' f n
  map_cone := hf

/-- The integral part of a fan morphism built from a map of integral vectors is that map. -/
@[simp]
theorem ofLatticeMap_latticeMap (Φ : Fan i) (Ψ : Fan i') (f : N →+ N')
    (hf : ∀ ⦃σ⦄, σ ∈ Φ.cones → ∃ τ ∈ Ψ.cones, σ.map (Φ.lattice.extend i' f) ≤ τ) :
    (ofLatticeMap Φ Ψ f hf).latticeMap = f := rfl

/-- The identity morphism of a fan. -/
@[expose]
protected def id (Φ : Fan i) : FanHom Φ Φ where
  latticeMap := AddMonoidHom.id N
  realMap := LinearMap.id
  map_lattice _ := rfl
  map_cone _ hσ := ⟨_, hσ, (PointedCone.map_id _).le⟩

/-- The integral part of the identity morphism is the identity. -/
@[simp]
theorem id_latticeMap (Φ : Fan i) : (FanHom.id Φ).latticeMap = AddMonoidHom.id N := rfl

/-- The real-linear part of the identity morphism is the identity. -/
@[simp]
theorem id_realMap (Φ : Fan i) : (FanHom.id Φ).realMap = LinearMap.id := rfl

section Comp

variable {N'' V'' : Type*} [AddCommGroup N''] [AddCommGroup V''] [Module ℝ V'']
  {i'' : N'' →+ V''} {Ω : Fan i''}

/-- The composite of two fan morphisms. -/
@[expose]
def comp (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) : FanHom Φ Ω where
  latticeMap := g.latticeMap.comp f.latticeMap
  realMap := g.realMap ∘ₗ f.realMap
  map_lattice n := by
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_comp]
    rw [f.map_lattice, g.map_lattice]
  map_cone σ hσ := by
    obtain ⟨τ, hτ, hστ⟩ := f.map_cone hσ
    obtain ⟨υ, hυ, hτυ⟩ := g.map_cone hτ
    refine ⟨υ, hυ, ?_⟩
    rw [← PointedCone.map_map]
    refine le_trans (fun y hy ↦ ?_) hτυ
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hστ hx, rfl⟩

/-- The integral part of a composite is the composite of the integral parts. -/
@[simp]
theorem comp_latticeMap (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (g.comp f).latticeMap = g.latticeMap.comp f.latticeMap := rfl

/-- The real-linear part of a composite is the composite of the real-linear parts. -/
@[simp]
theorem comp_realMap (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (g.comp f).realMap = g.realMap ∘ₗ f.realMap := rfl

/-- The identity morphism is a right unit for composition. -/
@[simp]
theorem comp_id (f : FanHom Φ Ψ) : f.comp (FanHom.id Φ) = f := ext rfl

/-- The identity morphism is a left unit for composition. -/
@[simp]
theorem id_comp (f : FanHom Φ Ψ) : (FanHom.id Ψ).comp f = f := ext rfl

variable {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V'''] [Module ℝ V''']
  {i''' : N''' →+ V'''} {Θ : Fan i'''}

/-- Composition of fan morphisms is associative. -/
theorem comp_assoc (h : FanHom Ω Θ) (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (h.comp g).comp f = h.comp (g.comp f) := ext rfl

end Comp

/-! ### Functoriality of the support -/

/-- A fan morphism carries the support of its source fan into the support of its target fan. -/
theorem mapsTo_support (f : FanHom Φ Ψ) : Set.MapsTo f.realMap Φ.support Ψ.support := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := Φ.mem_support.1 hx
  obtain ⟨τ, hτ, hστ⟩ := f.map_cone hσ
  exact Ψ.subset_support hτ (hστ ⟨x, hxσ, rfl⟩)

/-- The image of the support of the source fan is contained in the support of the target fan. -/
theorem image_support_subset (f : FanHom Φ Ψ) : f.realMap '' Φ.support ⊆ Ψ.support :=
  f.mapsTo_support.image_subset

/-! ### The least target cone of a source cone -/

/-- The cones of the target fan which contain the image of a fixed source cone have a least
element. A fan morphism therefore has a well-defined cone-by-cone description: each affine chart
of the source maps to a unique smallest affine chart of the target. -/
theorem exists_isLeast_cone (f : FanHom Φ Ψ) (hσ : σ ∈ Φ.cones) :
    ∃ τ, IsLeast {υ ∈ Ψ.cones | σ.map f.realMap ≤ υ} τ := by
  set T := {υ ∈ Ψ.cones | σ.map f.realMap ≤ υ}
  have hfin : T.Finite := Ψ.finite_cones.subset fun _ hυ ↦ hυ.1
  have hne : T.Nonempty := by
    obtain ⟨τ, hτ, hστ⟩ := f.map_cone hσ
    exact ⟨τ, hτ, hστ⟩
  obtain ⟨τ, hτT, hmin⟩ := hfin.exists_minimal hne
  refine ⟨τ, hτT, fun υ hυ ↦ ?_⟩
  have hinf : τ ⊓ υ ∈ T := ⟨Ψ.inf_mem hτT.1 hυ.1, le_inf hτT.2 hυ.2⟩
  exact le_trans (hmin hinf inf_le_left) inf_le_right

end FanHom

end TauCeti.Toric
