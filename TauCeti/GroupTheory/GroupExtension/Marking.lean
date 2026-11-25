/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Algebra.Quandle
public import TauCeti.GroupTheory.GroupExtension.UniversalCentralExtension
import TauCeti.Algebra.Group.Conj

/-!
# Marked central extensions and the universal marked extension

Let `c` be a subset of a group `G`, usually stable under conjugation. A *`c`-marking* of a
homomorphism `p : E →* G` chooses, for each `x ∈ c`, a lift `s x ∈ E` of `x`, equivariantly for
conjugation: if `e ∈ E` lies over `g` and `y = g x g⁻¹`, then `s y = e (s x) e⁻¹`. A *`c`-marked
central extension* of `G` is a central extension `p` (`MonoidHom.IsCentralExtension`) together
with a `c`-marking, and a morphism of marked central extensions is a homomorphism over `G` that
carries one marking to the other; it need not identify the kernels. When `c` is
conjugation-invariant, a marking is equivalently a conjugation-invariant subset of `E` that `p`
maps bijectively onto `c` (`MonoidHom.Marking.equivSet`).

The *universal marked extension* `U(G, c)` is the group presented by generators `[x]`, `x ∈ c`,
and the relations `[x][y][x]⁻¹ = [x y x⁻¹]`. No relation `[x] ^ (orderOf x) = 1` is imposed, and
indeed every generator has infinite order. The projection `[x] ↦ x` is a central extension when
`c` is conjugation-invariant and generates `G`, and for conjugation-invariant `c`, `x ↦ [x]` is a
marking of it. `U(G, c)` is initial among `c`-marked extensions: for every marking `s` of any
`p : E →* G` there is exactly one homomorphism `U(G, c) →* E` over `G` sending each `[x]` to
`s x`. Neither centrality, generation nor invariance is needed for this universal property.

For a conjugation-invariant `c`, `U(G, c)` is the enveloping group (Mathlib `Rack.EnvelGroup`) of
the conjugation quandle on `c` (`TauCeti.Quandle.conjOn`), and
`TauCeti.ReducedSchur.equivEnvelGroup` identifies the two. The presentation is the primary
definition here: it is defined for every subset `c`, without an invariance hypothesis, and it
comes with the `PresentedGroup` API for homomorphisms out of it and for generation by the `[x]`.

Let `D = c / G` be the set of conjugacy classes meeting `c`. The *class degree*
`U(G, c) →* ℤ^D` sends `[x]` to the basis vector of the class of `x`; composed with the map
`ℤ^D → G^{ab}` that sends the basis vector of a class to the image of any of its elements, it is
the abelianised projection.

`U(G, c)` carries the lifting invariant of a `c`-valued branch tuple, the ordered product of the
marked generators of its entries, which Wood uses to classify braid orbits of generating tuples
with large class multiplicities; the degree records the class multiplicities of the tuple.

## Main definitions

* `MonoidHom.Marking p c`: the `c`-markings of a homomorphism `p : E →* G`.
* `MonoidHom.Marking.ofBijOn`, `MonoidHom.Marking.equivSet`: markings as conjugation-invariant
  subsets mapped bijectively onto `c`.
* `TauCeti.ReducedSchur.universalMarked c`: the universal marked extension `U(G, c)`, a
  `PresentedGroup` on the relations `TauCeti.ReducedSchur.universalRelations c`.
* `TauCeti.ReducedSchur.lift`: a map on the generators satisfying the conjugation relations
  extends to `U(G, c)`.
* `TauCeti.ReducedSchur.projection c`: the projection `U(G, c) →* G`.
* `TauCeti.ReducedSchur.equivEnvelGroup`: `U(G, c)` is the enveloping group of the conjugation
  quandle on `c`.
* `TauCeti.ReducedSchur.marking`: the marking `x ↦ [x]` of the projection.
* `MonoidHom.Marking.lift`: the homomorphism `U(G, c) →* E` determined by a marking.
* `MonoidHom.Marking.liftEquiv`: `MonoidHom.Marking.lift` as an isomorphism, when the marked lifts
  generate `E` and `E` maps back to `U(G, c)` compatibly with the markings.
* `TauCeti.ReducedSchur.classSet c`, `TauCeti.ReducedSchur.degree c`: the classes `D` meeting `c`
  and the class degree `U(G, c) →* ℤ^D`.
* `TauCeti.ReducedSchur.degreeToAbelianization c`: the map `ℤ^D → G^{ab}`.

## Main results

* `MonoidHom.Marking.existsUnique_comp_eq_and_forall_apply_of`: `U(G, c)` is initial among
  `c`-marked extensions.
* `MonoidHom.Marking.bijective_lift_of_existsUnique`: for conjugation-invariant `c`, a marking
  that is itself initial among `c`-marked extensions (with test groups in the universe of `E` and
  `G`) is isomorphic to `U(G, c)` through its marking.
* `TauCeti.ReducedSchur.of_eq_mul_of_mul_inv`: conjugating a generator by any `w ∈ U(G, c)`
  gives the generator of the conjugate by the projection of `w`.
* `TauCeti.ReducedSchur.isCentralExtension_projection`: the projection is a central extension when
  `c` is conjugation-invariant and generates `G`.
* `TauCeti.ReducedSchur.not_isOfFinOrder_of`: the generators have infinite order.
* `TauCeti.ReducedSchur.degreeToAbelianization_degree`: the degree followed by `ℤ^D → G^{ab}` is
  the abelianised projection, and `TauCeti.ReducedSchur.degreeToAbelianization_surjective` when
  `c` generates `G`.

## References

* M. M. Wood, *An algebraic lifting invariant of Ellenberg, Venkatesh, and Westerland*, Res.
  Math. Sci. 8 (2021), §2.
* M. D. Fried, H. Völklein, *The inverse Galois problem and rational points on moduli spaces*,
  Math. Ann. 290 (1991), Appendix.
-/

public section

open Subgroup

namespace MonoidHom

variable {E G : Type*} [Group E] [Group G]

/-- A **`c`-marking** of a homomorphism `p : E →* G`: a lift `s x ∈ E` of each `x ∈ c` such that
`s (g x g⁻¹) = e (s x) e⁻¹` whenever `e ∈ E` lies over `g`. A `c`-marked central extension is a
central extension `p` (`MonoidHom.IsCentralExtension`) together with a `c`-marking of `p`. -/
structure Marking (p : E →* G) (c : Set G) where
  /-- The marked lift of an element of `c`. -/
  toFun : c → E
  /-- The marked lift of `x` lies over `x`. -/
  map_toFun' (x : c) : p (toFun x) = x
  /-- The marking is equivariant for conjugation. -/
  toFun_conj' (e : E) (x y : c) (h : (y : G) = p e * x * (p e)⁻¹) :
    toFun y = e * toFun x * e⁻¹

namespace Marking

variable {p : E →* G} {c : Set G}

instance : FunLike (p.Marking c) c E where
  coe := toFun
  coe_injective s t h := by
    cases s
    cases t
    congr

@[simp]
theorem toFun_eq_coe (s : p.Marking c) : s.toFun = s :=
  rfl

@[simp]
theorem coe_mk (f : c → E) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : p.Marking c) = f :=
  rfl

@[ext]
theorem ext {s t : p.Marking c} (h : ∀ x, s x = t x) : s = t :=
  DFunLike.ext _ _ h

/-- The marked lift of `x` lies over `x`. -/
@[simp]
theorem map_apply (s : p.Marking c) (x : c) : p (s x) = x :=
  s.map_toFun' x

/-- If `e` lies over `g`, the marked lift of `g x g⁻¹` is `e` conjugate of the marked lift of
`x`. -/
theorem apply_eq_mul_apply_mul_inv (s : p.Marking c) (e : E) {x y : c}
    (h : (y : G) = p e * x * (p e)⁻¹) : s y = e * s x * e⁻¹ :=
  s.toFun_conj' e x y h

/-- Distinct elements of `c` have distinct marked lifts. -/
theorem injective (s : p.Marking c) : Function.Injective s := fun x y h ↦
  Subtype.ext (by simpa using congr_arg p h)

/-- The marked lifts form a subset of `E` that `p` maps bijectively onto `c`. -/
theorem bijOn_range (s : p.Marking c) : Set.BijOn p (Set.range s) c := by
  refine ⟨?_, ?_, fun x hx ↦ ⟨s ⟨x, hx⟩, Set.mem_range_self _, s.map_apply _⟩⟩
  · rintro _ ⟨x, rfl⟩
    simp
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    rw [Subtype.ext (by simpa using h : (x : G) = y)]

/-- When `c` is conjugation-invariant, the set of marked lifts is conjugation-invariant. -/
theorem mul_apply_mul_inv_mem_range (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (s : p.Marking c)
    (e : E) (x : c) : e * s x * e⁻¹ ∈ Set.range s :=
  ⟨⟨p e * x * (p e)⁻¹, hc _ _ x.property⟩, s.apply_eq_mul_apply_mul_inv e rfl⟩

/-- Two homomorphisms out of `E` agree if they agree on the marked lifts, provided these
generate `E`. -/
theorem hom_ext {M : Type*} [Monoid M] (s : p.Marking c) (hs : closure (Set.range s) = ⊤)
    {f f' : E →* M} (h : ∀ x, f (s x) = f' (s x)) : f = f' :=
  eq_of_eqOn_dense hs (by rintro _ ⟨x, rfl⟩; exact h x)

section OfBijOn

variable {S : Set E} (hS : ∀ e, ∀ y ∈ S, e * y * e⁻¹ ∈ S) (h : Set.BijOn p S c)

/-- The marking given by a conjugation-invariant subset `S` of `E` that `p` maps bijectively onto
`c`: the marked lift of `x` is the element of `S` over `x`. -/
noncomputable def ofBijOn : p.Marking c where
  toFun x := (h.surjOn x.property).choose
  map_toFun' x := (h.surjOn x.property).choose_spec.2
  toFun_conj' e x y hy := by
    have hx := (h.surjOn x.property).choose_spec
    have hy' := (h.surjOn y.property).choose_spec
    exact h.injOn hy'.1 (hS e _ hx.1) (by rw [hy'.2, hy]; simp [hx.2])

theorem ofBijOn_mem (x : c) : ofBijOn hS h x ∈ S :=
  (h.surjOn x.property).choose_spec.1

/-- The marking given by `S` is the element of `S` over `x`. -/
theorem ofBijOn_eq_iff {x : c} {e : E} (he : e ∈ S) : ofBijOn hS h x = e ↔ p e = x :=
  ⟨fun hx ↦ hx ▸ (ofBijOn hS h).map_apply x, fun hx ↦
    h.injOn (ofBijOn_mem hS h x) he (by rw [map_apply, hx])⟩

@[simp]
theorem range_ofBijOn : Set.range (ofBijOn hS h) = S := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 (ofBijOn_mem hS h)) fun e he ↦ ?_
  exact ⟨⟨p e, h.mapsTo he⟩, (ofBijOn_eq_iff hS h he).2 rfl⟩

end OfBijOn

/-- For a conjugation-invariant `c`, the `c`-markings of `p` are the conjugation-invariant
subsets of `E` that `p` maps bijectively onto `c`. -/
noncomputable def equivSet (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) :
    p.Marking c ≃ {S : Set E // (∀ e, ∀ y ∈ S, e * y * e⁻¹ ∈ S) ∧ Set.BijOn p S c} where
  toFun s := ⟨Set.range s, by
    rintro e _ ⟨x, rfl⟩
    exact s.mul_apply_mul_inv_mem_range hc e x, s.bijOn_range⟩
  invFun S := ofBijOn S.property.1 S.property.2
  left_inv s := ext fun x ↦ (ofBijOn_eq_iff _ s.bijOn_range (Set.mem_range_self x)).2 (by simp)
  right_inv S := Subtype.ext (range_ofBijOn S.property.1 S.property.2)

@[simp]
theorem coe_equivSet_apply (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (s : p.Marking c) :
    (equivSet hc s : Set E) = Set.range s :=
  (rfl)

@[simp]
theorem equivSet_symm_apply (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c)
    (S : {S : Set E // (∀ e, ∀ y ∈ S, e * y * e⁻¹ ∈ S) ∧ Set.BijOn p S c}) :
    (equivSet hc).symm S = ofBijOn S.property.1 S.property.2 :=
  (rfl)

/-- The inclusion of `c` is a `c`-marking of the identity of `G`. -/
def inclusion (c : Set G) : (MonoidHom.id G).Marking c where
  toFun := Subtype.val
  map_toFun' _ := rfl
  toFun_conj' _ _ _ h := h

@[simp]
theorem inclusion_apply (c : Set G) (x : c) : inclusion c x = x :=
  (rfl)

end Marking

end MonoidHom

namespace TauCeti

namespace ReducedSchur

variable {G H : Type*} [Group G] [Group H]

/-- The relations `[x][y][x]⁻¹ = [z]`, for `x, y, z ∈ c` with `z = x y x⁻¹`, of the universal
marked extension. -/
def universalRelations (c : Set G) : Set (FreeGroup c) :=
  {w | ∃ x y z : c, (z : G) = x * y * (x : G)⁻¹ ∧
    w = FreeGroup.of x * FreeGroup.of y * (FreeGroup.of x)⁻¹ * (FreeGroup.of z)⁻¹}

/-- The **universal marked extension** `U(G, c)`: the group on generators `[x]`, `x ∈ c`, subject
only to the conjugation relations `[x][y][x]⁻¹ = [x y x⁻¹]`. -/
abbrev universalMarked (c : Set G) : Type _ :=
  PresentedGroup (universalRelations c)

variable {c : Set G}

/-- The conjugation relations hold between the generators of `U(G, c)`. -/
theorem of_eq_of_mul_of_mul_inv {x y z : c} (h : (z : G) = x * y * (x : G)⁻¹) :
    (PresentedGroup.of z : universalMarked c) =
      PresentedGroup.of x * PresentedGroup.of y * (PresentedGroup.of x)⁻¹ := by
  have := PresentedGroup.one_of_mem (rels := universalRelations c) ⟨x, y, z, h, rfl⟩
  simp only [map_mul, map_inv] at this
  exact (mul_inv_eq_one.1 this).symm

/-- A map on the generators of `U(G, c)` satisfying the conjugation relations extends to a
homomorphism. -/
def lift (f : c → H)
    (hf : ∀ x y z : c, (z : G) = x * y * (x : G)⁻¹ → f z = f x * f y * (f x)⁻¹) :
    universalMarked c →* H :=
  PresentedGroup.toGroup (f := f) <| by
    rintro _ ⟨x, y, z, h, rfl⟩
    simp [hf x y z h]

@[simp]
theorem lift_of (f : c → H)
    (hf : ∀ x y z : c, (z : G) = x * y * (x : G)⁻¹ → f z = f x * f y * (f x)⁻¹) (x : c) :
    lift f hf (PresentedGroup.of x) = f x :=
  PresentedGroup.toGroup.of _

/-- A homomorphism out of `U(G, c)` is the lift of `f` exactly when it sends each generator `[x]`
to `f x`. -/
theorem eq_lift_iff (f : c → H)
    (hf : ∀ x y z : c, (z : G) = x * y * (x : G)⁻¹ → f z = f x * f y * (f x)⁻¹)
    {g : universalMarked c →* H} : g = lift f hf ↔ ∀ x, g (PresentedGroup.of x) = f x :=
  ⟨by rintro rfl; simp, fun h ↦ PresentedGroup.ext fun x ↦ by simp [h]⟩

/-- **Induction on `U(G, c)` along the generators**: a property of the generators `[x]` that is
closed under `1`, products and inverses holds on all of `U(G, c)`. -/
@[elab_as_elim]
theorem induction_on {motive : universalMarked c → Prop} (u : universalMarked c)
    (of : ∀ x, motive (PresentedGroup.of x)) (one : motive 1)
    (mul : ∀ a b, motive a → motive b → motive (a * b)) (inv : ∀ a, motive a → motive a⁻¹) :
    motive u :=
  closure_induction (p := fun u _ ↦ motive u) (by rintro _ ⟨x, rfl⟩; exact of x) one
    (fun a b _ _ ↦ mul a b) (fun a _ ↦ inv a)
    ((PresentedGroup.closure_range_of _).symm ▸ mem_top u)

variable (c) in
/-- The projection `U(G, c) →* G`, `[x] ↦ x`. -/
def projection : universalMarked c →* G :=
  lift Subtype.val fun _ _ _ h ↦ h

@[simp]
theorem projection_of (x : c) : projection c (PresentedGroup.of x) = x :=
  lift_of _ _ x

/-- The projection of `U(G, c)` is surjective when `c` generates `G`. -/
theorem projection_surjective (hgen : closure c = ⊤) : Function.Surjective (projection c) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
  exact fun x hx ↦ ⟨PresentedGroup.of ⟨x, hx⟩, projection_of _⟩

/-- **Conjugation of a generator.** For a conjugation-invariant `c` and any `w ∈ U(G, c)`,
`w [x] w⁻¹ = [π(w) x π(w)⁻¹]`, where `π` is the projection. -/
theorem of_eq_mul_of_mul_inv (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (w : universalMarked c)
    {x y : c} (h : (y : G) = projection c w * x * (projection c w)⁻¹) :
    (PresentedGroup.of y : universalMarked c) = w * PresentedGroup.of x * w⁻¹ := by
  induction w using induction_on generalizing x y with
  | of a => exact of_eq_of_mul_of_mul_inv (by simpa using h)
  | one =>
    simp only [map_one, one_mul, inv_one, mul_one] at h ⊢
    rw [Subtype.ext h]
  | mul a b iha ihb =>
    rw [iha (x := ⟨projection c b * x * (projection c b)⁻¹, hc _ _ x.property⟩)
      (by simp [h, mul_assoc]), ihb rfl]
    group
  | inv a iha =>
    rw [iha (x := y) (y := x) (by simp [h, mul_assoc]), inv_inv]
    group

/-- When `c` is conjugation-invariant, `x ↦ [x]` is a `c`-marking of the projection of
`U(G, c)`. -/
def marking (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) : (projection c).Marking c where
  toFun := PresentedGroup.of
  map_toFun' := projection_of
  toFun_conj' w _ _ h := of_eq_mul_of_mul_inv hc w h

@[simp]
theorem marking_apply (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (x : c) :
    marking hc x = PresentedGroup.of x :=
  (rfl)

/-- For a conjugation-invariant `c`, the kernel of the projection of `U(G, c)` is central. -/
theorem ker_projection_le_center (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) :
    (projection c).ker ≤ center (universalMarked c) := by
  intro w hw
  refine mem_center_iff.2 fun u ↦ ?_
  induction u using induction_on with
  | of x =>
    exact eq_mul_inv_iff_mul_eq.1
      (of_eq_mul_of_mul_inv hc w (x := x) (y := x) (by simp [(MonoidHom.mem_ker).1 hw]))
  | one => simp
  | mul a b iha ihb => exact Commute.mul_left iha ihb
  | inv a iha => exact Commute.inv_left iha

/-- **The universal marked extension is a central extension** when `c` is conjugation-invariant
and generates `G`. -/
theorem isCentralExtension_projection (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c)
    (hgen : closure c = ⊤) : (projection c).IsCentralExtension :=
  ⟨projection_surjective hgen, ker_projection_le_center hc⟩

/-! ### Comparison with the enveloping group of the conjugation quandle -/

/-- For a conjugation-invariant `c`, `U(G, c)` is Mathlib's enveloping group `Rack.EnvelGroup` of
the conjugation quandle on `c`, the generator `[x]` corresponding to the image of `x`. -/
noncomputable def equivEnvelGroup (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) :
    universalMarked c ≃* @Rack.EnvelGroup c (Quandle.conjOn c hc).toRack :=
  letI := Quandle.conjOn c hc
  let F : ShelfHom c (Quandle.Conj (universalMarked c)) :=
    ⟨PresentedGroup.of, fun {x y} ↦ by
      rw [_root_.Quandle.conj_act_eq_conj]
      exact of_eq_of_mul_of_mul_inv (Quandle.coe_conjOn_act x y)⟩
  let φ : universalMarked c →* Rack.EnvelGroup c := lift (Rack.toEnvelGroup c) fun x y z h ↦ by
    rw [show z = Shelf.act x y from Subtype.ext (h.trans (Quandle.coe_conjOn_act x y).symm)]
    exact (Rack.toEnvelGroup c).map_act
  have hφ (x : c) : φ (PresentedGroup.of x) = Rack.toEnvelGroup c x := lift_of _ _ x
  -- `Rack.toEnvelGroup.map F` sends the image of `x` in the enveloping group to `[x]`: this is
  -- `Rack.toEnvelGroup.univ`, read off on the underlying functions.
  have hF (x : c) : Rack.toEnvelGroup.map F (Rack.toEnvelGroup c x) = PresentedGroup.of x :=
    congr($(Rack.toEnvelGroup.univ c _ F).toFun x)
  MonoidHom.toMulEquiv φ (Rack.toEnvelGroup.map F)
    (PresentedGroup.ext fun x ↦ by simp [hφ, hF])
    -- A homomorphism `g` out of the enveloping group is determined by
    -- `Rack.toEnvelGroup.map.symm g = (Quandle.Conj.map g).comp (Rack.toEnvelGroup c)`, whose
    -- underlying function is `g ∘ Rack.toEnvelGroup c` by definition. So it suffices that
    -- `φ ∘ Rack.toEnvelGroup.map F` fixes each `Rack.toEnvelGroup c x`.
    (Rack.toEnvelGroup.map.symm.injective <| ShelfHom.ext <| funext fun x ↦
      (congrArg φ (hF x)).trans (hφ x))

@[simp]
theorem equivEnvelGroup_of (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (x : c) :
    equivEnvelGroup hc (PresentedGroup.of x) =
      @Rack.toEnvelGroup c (Quandle.conjOn c hc).toRack x := by
  simp [equivEnvelGroup]

@[simp]
theorem equivEnvelGroup_symm_toEnvelGroup (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (x : c) :
    (equivEnvelGroup hc).symm (@Rack.toEnvelGroup c (Quandle.conjOn c hc).toRack x) =
      PresentedGroup.of x :=
  (MulEquiv.symm_apply_eq _).2 (equivEnvelGroup_of hc x).symm

end ReducedSchur

end TauCeti

namespace MonoidHom.Marking

open TauCeti.ReducedSchur

variable {E G : Type*} [Group E] [Group G] {p : E →* G} {c : Set G}

/-- The homomorphism `U(G, c) →* E` sending `[x]` to the marked lift of `x`. -/
def lift (s : p.Marking c) : universalMarked c →* E :=
  TauCeti.ReducedSchur.lift s fun x _ _ h ↦ s.apply_eq_mul_apply_mul_inv (s x) (by simpa using h)

@[simp]
theorem lift_of (s : p.Marking c) (x : c) : s.lift (PresentedGroup.of x) = s x :=
  TauCeti.ReducedSchur.lift_of _ _ x

/-- The homomorphism determined by a marking lies over `G`. -/
@[simp]
theorem comp_lift (s : p.Marking c) : p.comp s.lift = projection c := by
  ext x
  simp

/-- A homomorphism out of `U(G, c)` is the one determined by `s` exactly when it sends each
generator `[x]` to the marked lift of `x`. -/
theorem eq_lift_iff (s : p.Marking c) {f : universalMarked c →* E} :
    f = s.lift ↔ ∀ x, f (PresentedGroup.of x) = s x :=
  TauCeti.ReducedSchur.eq_lift_iff _ _

/-- **`U(G, c)` is initial among `c`-marked extensions**: for every `c`-marking `s` of a
homomorphism `p : E →* G` there is exactly one homomorphism `U(G, c) →* E` over `G` sending each
generator `[x]` to `s x`. -/
theorem existsUnique_comp_eq_and_forall_apply_of (s : p.Marking c) :
    ∃! f : universalMarked c →* E, p.comp f = projection c ∧
      ∀ x, f (PresentedGroup.of x) = s x :=
  ⟨s.lift, ⟨s.comp_lift, s.lift_of⟩, fun _ hf ↦ s.eq_lift_iff.2 hf.2⟩

@[simp]
theorem lift_marking (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) :
    (marking hc).lift = MonoidHom.id (universalMarked c) := by
  ext x
  simp

@[simp]
theorem lift_inclusion : (inclusion c).lift = projection c := by
  ext x
  simp

/-- **Recognising `U(G, c)`.** If the marked lifts of `s` generate `E` and some homomorphism
`g : E →* U(G, c)` sends each `s x` to `[x]`, then `s.lift` is an isomorphism `U(G, c) ≃* E`, with
inverse `g`. It is the only homomorphism `U(G, c) →* E` sending each `[x]` to `s x`
(`MonoidHom.Marking.eq_lift_iff`). For conjugation-invariant `c`, when `s` is itself initial
among `c`-marked extensions whose groups lie in the universe of `E` and `G`, `s.lift` is
bijective (`MonoidHom.Marking.bijective_lift_of_existsUnique`), so any two such universal marked
extensions are uniquely isomorphic through their markings. -/
def liftEquiv (s : p.Marking c) (hs : closure (Set.range s) = ⊤) (g : E →* universalMarked c)
    (hg : ∀ x, g (s x) = PresentedGroup.of x) : universalMarked c ≃* E :=
  MonoidHom.toMulEquiv s.lift g (PresentedGroup.ext fun x ↦ by simp [hg])
    (s.hom_ext hs fun x ↦ by simp [hg])

@[simp]
theorem coe_liftEquiv (s : p.Marking c) (hs : closure (Set.range s) = ⊤)
    (g : E →* universalMarked c) (hg : ∀ x, g (s x) = PresentedGroup.of x) :
    ⇑(s.liftEquiv hs g hg) = s.lift :=
  (rfl)

@[simp]
theorem coe_liftEquiv_symm (s : p.Marking c) (hs : closure (Set.range s) = ⊤)
    (g : E →* universalMarked c) (hg : ∀ x, g (s x) = PresentedGroup.of x) :
    ⇑(s.liftEquiv hs g hg).symm = g :=
  (rfl)

theorem liftEquiv_of (s : p.Marking c) (hs : closure (Set.range s) = ⊤)
    (g : E →* universalMarked c) (hg : ∀ x, g (s x) = PresentedGroup.of x) (x : c) :
    s.liftEquiv hs g hg (PresentedGroup.of x) = s x := by
  simp

theorem liftEquiv_symm_apply (s : p.Marking c) (hs : closure (Set.range s) = ⊤)
    (g : E →* universalMarked c) (hg : ∀ x, g (s x) = PresentedGroup.of x) (x : c) :
    (s.liftEquiv hs g hg).symm (s x) = PresentedGroup.of x := by
  simp [hg]

end MonoidHom.Marking

namespace MonoidHom.Marking

open TauCeti.ReducedSchur

universe u

variable {E G : Type u} [Group E] [Group G] {p : E →* G} {c : Set G}

/-- **Uniqueness of the universal marked extension.** For a conjugation-invariant `c`, if a
`c`-marking `s` of `p : E →* G` is itself initial among `c`-marked extensions, that is every
`c`-marking `t` of any `q : F →* G` is the image of `s` under exactly one homomorphism `E →* F`
over `G`, then `s.lift : U(G, c) →* E` is bijective. The groups `F` range over the universe of
`E` and `G`, which contains `U(G, c)`. -/
theorem bijective_lift_of_existsUnique (hc : ∀ g x, x ∈ c → g * x * g⁻¹ ∈ c) (s : p.Marking c)
    (h : ∀ (F : Type u) [Group F] (q : F →* G) (t : q.Marking c),
      ∃! f : E →* F, q.comp f = p ∧ ∀ x, f (s x) = t x) :
    Function.Bijective s.lift := by
  obtain ⟨g, ⟨hgp, hg⟩, -⟩ := h _ (projection c) (marking hc)
  have hgs : g.comp s.lift = MonoidHom.id _ := PresentedGroup.ext fun x ↦ by simp [hg]
  have hsg : s.lift.comp g = MonoidHom.id E :=
    (h E p s).unique ⟨by rw [← MonoidHom.comp_assoc, comp_lift, hgp], fun x ↦ by simp [hg]⟩
      ⟨rfl, fun _ ↦ rfl⟩
  exact Function.bijective_iff_has_inverse.2
    ⟨g, fun u ↦ DFunLike.congr_fun hgs u, fun e ↦ DFunLike.congr_fun hsg e⟩

end MonoidHom.Marking

namespace TauCeti

namespace ReducedSchur

variable {G : Type*} [Group G]

/-! ### The class degree -/

/-- The conjugacy classes meeting `c`, the index set `D = c / G` of the class degree. -/
def classSet (c : Set G) : Set (ConjClasses G) :=
  ConjClasses.mk '' c

variable {c : Set G}

@[simp]
theorem mem_classSet_iff {d : ConjClasses G} : d ∈ classSet c ↔ ∃ x ∈ c, ConjClasses.mk x = d :=
  Iff.rfl

/-- The class of an element of `c`, as an element of `D = c / G`. -/
def toClassSet (x : c) : classSet c :=
  ⟨ConjClasses.mk x, x, x.property, rfl⟩

@[simp]
theorem coe_toClassSet (x : c) : (toClassSet x : ConjClasses G) = ConjClasses.mk (x : G) :=
  (rfl)

theorem toClassSet_surjective : Function.Surjective (toClassSet (c := c)) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[simp]
theorem toClassSet_eq_toClassSet_iff {x y : c} : toClassSet x = toClassSet y ↔ IsConj (x : G) y :=
  Subtype.ext_iff.trans ConjClasses.mk_eq_mk_iff_isConj

variable (c) in
/-- The **class degree** `U(G, c) →* ℤ^D`, sending each generator `[x]` to the basis vector of the
class of `x`. The free abelian group `ℤ^D` is written multiplicatively. -/
noncomputable def degree : universalMarked c →* Multiplicative (classSet c →₀ ℤ) :=
  lift (fun x ↦ .ofAdd (Finsupp.single (toClassSet x) 1)) fun x y z h ↦ by
    rw [toClassSet_eq_toClassSet_iff.2 (isConj_iff.2 ⟨(x : G), h.symm⟩).symm,
      mul_inv_cancel_comm]

@[simp]
theorem degree_of (x : c) :
    degree c (PresentedGroup.of x) = .ofAdd (Finsupp.single (toClassSet x) 1) :=
  lift_of _ _ x

/-- The generators `[x]` of `U(G, c)` have infinite order: `[x] ^ n ≠ 1` for every `n ≥ 1`. -/
theorem not_isOfFinOrder_of (x : c) : ¬IsOfFinOrder (PresentedGroup.of x : universalMarked c) := by
  rw [← orderOf_eq_zero_iff, orderOf_eq_zero_iff']
  intro n hn h
  have := congr(Multiplicative.toAdd (degree c $h) (toClassSet x))
  simp at this
  omega

variable (c) in
/-- The map `ℤ^D → G^{ab}` sending the basis vector of a class to the image of any of its
elements in the abelianization. -/
noncomputable def degreeToAbelianization :
    (classSet c →₀ ℤ) →ₗ[ℤ] Additive (Group.Abelianization G) :=
  Finsupp.linearCombination ℤ fun d ↦
    .ofMul (ConjClasses.mkEquiv.symm (ConjClasses.map Group.Abelianization.of d.val))

@[simp]
theorem degreeToAbelianization_single (x : c) (n : ℤ) :
    degreeToAbelianization c (Finsupp.single (toClassSet x) n) =
      n • .ofMul (Group.Abelianization.of (x : G)) := by
  rw [degreeToAbelianization, Finsupp.linearCombination_single, coe_toClassSet,
    ConjClasses.map_mk]
  -- The forward map of `ConjClasses.mkEquiv` is `ConjClasses.mk` by definition.
  exact congr_arg (n • Additive.ofMul ·) (ConjClasses.mkEquiv.symm_apply_apply _)

/-- **The degree followed by `ℤ^D → G^{ab}` is the abelianised projection.** -/
@[simp]
theorem degreeToAbelianization_degree (u : universalMarked c) :
    degreeToAbelianization c (degree c u).toAdd =
      .ofMul (Group.Abelianization.of (projection c u)) := by
  induction u using induction_on with
  | of x => simp
  | one => simp
  | mul a b iha ihb => simp [iha, ihb]
  | inv a iha => simp [iha]

/-- When `c` generates `G`, every element of `G^{ab}` is the image of a degree vector. -/
theorem degreeToAbelianization_surjective (hgen : closure c = ⊤) :
    Function.Surjective (degreeToAbelianization c) := by
  intro a
  obtain ⟨g, hg⟩ := Group.Abelianization.surjective_of G a.toMul
  obtain ⟨u, rfl⟩ := projection_surjective hgen g
  exact ⟨(degree c u).toAdd, by rw [degreeToAbelianization_degree, hg, ofMul_toMul]⟩

end ReducedSchur

end TauCeti
