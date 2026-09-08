/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Kronecker.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Representation
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# The line representations of the generalized Kronecker quiver

Put the base field at both vertices of the generalized Kronecker quiver, let one distinguished
arrow act by multiplication by a scalar `c` and every other arrow by the identity. This file
builds that representation, `TauCeti.kroneckerLineRep`. Every member of the family is
indecomposable as soon as its scalar is nonzero or the quiver carries an arrow other than the
distinguished one, and on a quiver carrying such a second arrow the family is pairwise
non-isomorphic:

`kroneckerLineRep k a₁ c ≅ kroneckerLineRep k a₁ d ↔ c = d`.

Every member of the family has dimension vector `(1, 1)`. So on a quiver with at least two arrows
the dimension vector of a finite-dimensional indecomposable **does not determine it**, and its
Tits value is `2 - #arrows`, not `1`. Both facts are sharpness statements: the Gabriel injection
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic` and the real-root property
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic` are proved for an acyclic
quiver whose Tits form is *positive definite*, and the Kronecker quiver -- acyclic, with the
positive semidefinite Tits form `(a - b) ^ 2` of `TauCeti.Quiver.Kronecker.titsForm_apply` --
shows that neither survives the weakening of that hypothesis to acyclicity alone.

The family is the affine chart of the `ℙ¹`-family the Kronecker quiver is known for, and only that
chart: letting the two arrows of `• ⇉ •` act by a pair of scalars `(c₀, c₁)`, rescaling that pair
by a unit produces an isomorphic representation, so the classes are the points `[c₀ : c₁]` of the
projective line. Normalizing the non-distinguished arrows to the identity picks the chart
`c₁ ≠ 0` and parametrizes it by `c = c₀ / c₁`. Neither the one class this omits -- the point at
infinity, where the distinguished arrow acts by the identity and every other arrow by zero -- nor
the exhaustiveness of the resulting list, is built here.

The member at `c = 0` is the smallest Jordan block `TauCeti.kroneckerJordanRep k a₁ 0` of
`TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType`, up to the identification of
`k[X]/(X)` with `k`. That file settles the representation type of the quiver with the blocks of
every size, which grow in dimension, and records there that the lines below would only settle it
over an infinite base field. The point of the lines is the other one: they are infinitely many
indecomposables *at a single dimension vector* when the field is infinite, and already two of
them over any field at all.

## Main definitions

* `TauCeti.kroneckerLineRep`: the line `k` at both vertices of the generalized Kronecker quiver,
  the distinguished arrow acting by a scalar and every other arrow by the identity.
* `TauCeti.kroneckerLineRepScalar`: the scalar recording a morphism between two line
  representations, the value at `1` of its component at the source vertex.
* `TauCeti.kroneckerLineRepHom`: conversely, the morphism of line representations attached to a
  scalar intertwining the two actions of the distinguished arrow.

## Main results

* `TauCeti.kroneckerLineRep_hom_app_src_apply`, `TauCeti.kroneckerLineRep_hom_ext` and
  `TauCeti.kroneckerLineRepScalar_intertwine`: a morphism of line representations is
  multiplication by its scalar at the source vertex; that scalar determines the morphism as soon
  as the distinguished arrow acts invertibly or some other arrow exists, and satisfies
  `c * s = d * s` for the two scalars `c` and `d` of its source and target.
* `TauCeti.kroneckerLineRepScalar_kroneckerLineRepHom` and
  `TauCeti.kroneckerLineRepHom_kroneckerLineRepScalar`: the converse identification, on a quiver
  carrying an arrow other than the distinguished one, of those morphisms with the scalars `s`
  satisfying `c * s = d * s`.
* `TauCeti.indecomposable_kroneckerLineRep`: a line representation is indecomposable as soon as
  its scalar is nonzero or some arrow other than the distinguished one exists; its endomorphisms
  are recorded faithfully by a single scalar.
* `TauCeti.nonempty_kroneckerLineRep_iso_iff`: **on a quiver carrying an arrow other than the
  distinguished one, two of them are isomorphic exactly when their scalars agree.**
* `TauCeti.dimVector_kroneckerLineRep`: every line representation has dimension vector `1` at
  both vertices.
* `TauCeti.exists_indecomposable_dimVector_eq_not_nonempty_iso_kronecker`: **on a generalized
  Kronecker quiver with two distinct arrows the dimension vector does not determine an
  indecomposable**:
  over every field such a quiver carries two non-isomorphic finite-dimensional indecomposables of
  the same dimension vector.
* `TauCeti.titsForm_dimVector_kroneckerLineRep`: the Tits value of that common dimension vector is
  `2 - #arrows`, which is `1` only for the `A₂` quiver.

## Implementation notes

`TauCeti.kroneckerLineRep` carries `@[expose]`, for the reason
`TauCeti.RepresentationTheory.Quiver.Kronecker.Representation` records for
`TauCeti.kroneckerRep`: a functor built by `CategoryTheory.Paths.lift` reveals its value on
objects only through its definition, so without it every statement below reading a component of a
morphism as a linear map on `k` fails to elaborate.

## References

The affine chart of the `ℙ¹`-family of indecomposables of dimension vector `(1, 1)` of the
Kronecker quiver. See Derksen--Weyman, *An Introduction to Quiver Representations*, and
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. VIII.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {k : Type u} [Field k] {A : Type v}

/-! ### The line representations -/

-- The distinguished arrow is singled out by an `if`, so a `Decidable` instance for equality in `A`
-- is needed; it is taken classically rather than imposed as a hypothesis on `A`, as
-- `TauCeti.kroneckerJordanRep` does. The two lemmas below discharge the `if` in either direction,
-- so no statement in this file mentions the instance.
open Classical in
variable (k) in
/-- **The line representation of the generalized Kronecker quiver at a scalar `c`**: the base field
at both vertices, with the arrow `a₁` acting by multiplication by `c` and every other arrow by the
identity. -/
@[expose]
noncomputable def kroneckerLineRep (a₁ : A) (c : k) : QuiverRep k (Quiver.Kronecker A) :=
  kroneckerRep k (ModuleCat.of k k) (ModuleCat.of k k)
    fun a ↦ if a = a₁ then ModuleCat.ofHom (LinearMap.mulLeft k c) else 𝟙 _

variable {a₀ a₁ : A} {c d : k}

-- Not `@[simp]`: this and `TauCeti.kroneckerLineRep_map_arrowPath_of_ne` rewrite inside the
-- `ModuleCat.Hom.hom` of the two `_apply` lemmas below, taking those left-hand sides out of
-- simp-normal form (`simpNF`), exactly as the corresponding pair for the Jordan blocks does.
/-- The distinguished arrow acts on a line representation by multiplication by its scalar. -/
theorem kroneckerLineRep_map_arrowPath_self :
    (kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₁) =
      ModuleCat.ofHom (LinearMap.mulLeft k c) :=
  (kroneckerRep_map_arrowPath _ _ _ a₁).trans (ite_eq_left rfl)

/-- The action of the distinguished arrow, read on an element. -/
@[simp]
theorem kroneckerLineRep_map_arrowPath_self_apply (x : k) :
    ((kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₁)).hom x = c * x := by
  rw [kroneckerLineRep_map_arrowPath_self]
  rfl

/-- Every other arrow acts on a line representation by the identity. -/
theorem kroneckerLineRep_map_arrowPath_of_ne (h : a₀ ≠ a₁) :
    (kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₀) = 𝟙 (ModuleCat.of k k) :=
  (kroneckerRep_map_arrowPath _ _ _ a₀).trans (ite_eq_right h)

/-- The action of any other arrow, read on an element. -/
@[simp]
theorem kroneckerLineRep_map_arrowPath_of_ne_apply (h : a₀ ≠ a₁) (x : k) :
    ((kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₀)).hom x = x := by
  rw [kroneckerLineRep_map_arrowPath_of_ne (c := c) h]
  exact ModuleCat.id_apply (ModuleCat.of k k) x

/-- A line representation is finite-dimensional: both of its vertex spaces are the base field. -/
theorem isFinDim_kroneckerLineRep :
    IsFinDim k (Quiver.Kronecker A) (kroneckerLineRep k a₁ c) := by
  refine isFinDim_iff.mpr fun w ↦ ?_
  cases w <;> exact inferInstanceAs (FiniteDimensional k k)

-- Not `@[simp]`: `TauCeti.dimVector_apply` already is, so `simp` unfolds `dimVector` to a
-- `Module.finrank` before this could fire, exactly as for `TauCeti.dimVector_kroneckerJordanRep`.
/-- **The dimension vector of a line representation is `1` at both vertices.** The whole family
therefore sits at the single dimension vector `(1, 1)`. -/
theorem dimVector_kroneckerLineRep (w : Quiver.Kronecker A) :
    dimVector (kroneckerLineRep k a₁ c) w = 1 := by
  rw [dimVector_apply]
  cases w <;> exact Module.finrank_self k

/-- A line representation is nonzero: its vertex spaces are the base field. -/
theorem not_isZero_kroneckerLineRep :
    ¬ IsZero (kroneckerLineRep k a₁ c) := by
  intro hz
  have : Subsingleton k :=
    ModuleCat.subsingleton_of_isZero (hz.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  exact false_of_nontrivial_of_subsingleton k

/-! ### The morphisms between two line representations -/

/-- **The scalar recording a morphism of line representations**: the value at `1` of its component
at the source vertex, that component being a linear endomorphism of the base field. The morphism is
multiplication by this scalar at the source (`TauCeti.kroneckerLineRep_hom_app_src_apply`), the
scalar determines the morphism whenever `TauCeti.kroneckerLineRep_hom_ext` applies, and it is
constrained by `TauCeti.kroneckerLineRepScalar_intertwine`; conversely
`TauCeti.kroneckerLineRepHom` builds the morphism back from a scalar meeting that constraint. -/
noncomputable def kroneckerLineRepScalar
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) : k :=
  (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom (1 : k)

/-- **A morphism of line representations acts at the source vertex by multiplication by its
scalar.** -/
@[simp]
theorem kroneckerLineRep_hom_app_src_apply
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) (x : k) :
    (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom x =
      x * kroneckerLineRepScalar e := by
  have hx : (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom (x • (1 : k)) =
      x • kroneckerLineRepScalar e := map_smul _ x (1 : k)
  rwa [smul_eq_mul, mul_one, smul_eq_mul] at hx

-- The three lemmas below read the component at the source vertex of the zero morphism, of the
-- identity and of a composite. Their category-level statements
-- `CategoryTheory.NatTrans.app_zero`, `CategoryTheory.NatTrans.id_app` and
-- `CategoryTheory.NatTrans.comp_app` do not *rewrite* at a vertex of `Paths`, that component not
-- being type-correct at the transparency `rw`/`simp` work at; they are therefore applied as terms,
-- which elaborates, and the passage from the resulting morphism of `ModuleCat` to its linear map
-- is `ModuleCat.hom_zero`, `ModuleCat.hom_id` and `ModuleCat.comp_apply`.

/-- The zero morphism has scalar `0`. -/
@[simp]
theorem kroneckerLineRepScalar_zero :
    kroneckerLineRepScalar (0 : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) = 0 := by
  have h : kroneckerLineRepScalar (0 : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) =
      (ModuleCat.Hom.hom (0 : ModuleCat.of k k ⟶ ModuleCat.of k k)) (1 : k) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) (1 : k))
      (NatTrans.app_zero (F := kroneckerLineRep k a₁ c) (G := kroneckerLineRep k a₁ d)
        (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  rw [h, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The identity has scalar `1`. -/
@[simp]
theorem kroneckerLineRepScalar_id : kroneckerLineRepScalar (𝟙 (kroneckerLineRep k a₁ c)) = 1 := by
  have h : kroneckerLineRepScalar (𝟙 (kroneckerLineRep k a₁ c)) =
      (ModuleCat.Hom.hom (𝟙 (ModuleCat.of k k))) (1 : k) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) (1 : k))
      (NatTrans.id_app (kroneckerLineRep k a₁ c)
        (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  rw [h, ModuleCat.hom_id, LinearMap.id_apply]

/-- Composition multiplies the scalars. -/
@[simp]
theorem kroneckerLineRepScalar_comp {c' : k}
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d)
    (e' : kroneckerLineRep k a₁ d ⟶ kroneckerLineRep k a₁ c') :
    kroneckerLineRepScalar (e ≫ e') = kroneckerLineRepScalar e * kroneckerLineRepScalar e' := by
  have h : kroneckerLineRepScalar (e ≫ e') =
      (e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom
        (kroneckerLineRepScalar e : k) :=
    (congrArg (fun g ↦ (ModuleCat.Hom.hom g) (1 : k))
      (NatTrans.comp_app e e' (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))).trans
        (ModuleCat.comp_apply _ _ _)
  exact h.trans (kroneckerLineRep_hom_app_src_apply e' (kroneckerLineRepScalar e))

/-- **The two components of a morphism of line representations agree**, by naturality along an
arrow that acts as the identity on both. -/
theorem kroneckerLineRep_hom_app_tgt_of_ne (h : a₀ ≠ a₁)
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) := by
  have hnat := kroneckerRep_hom_naturality e a₀
  rw [ite_eq_right h, ite_eq_right h] at hnat
  exact (Category.id_comp _).symm.trans (hnat.trans (Category.comp_id _))

/-- **Naturality along the distinguished arrow**: a morphism from the line at `c` to the line at
`d` intertwines multiplication by `c` with multiplication by `d`. -/
private theorem app_tgt_comp_mulLeft (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    ModuleCat.ofHom (LinearMap.mulLeft k c) ≫
        e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ≫
        ModuleCat.ofHom (LinearMap.mulLeft k d) := by
  have hnat := kroneckerRep_hom_naturality e a₁
  rwa [ite_eq_left rfl, ite_eq_left rfl] at hnat

/-- **A morphism of line representations is determined by its component at the source vertex when
the distinguished arrow acts invertibly**: naturality along that arrow computes the component at
the target from the one at the source. -/
private theorem app_tgt_ext_of_ne_zero (hc : c ≠ 0)
    {e e' : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d}
    (hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) :
    e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) := by
  have hnat := app_tgt_comp_mulLeft e
  rw [hsrc, ← app_tgt_comp_mulLeft e'] at hnat
  refine ModuleCat.hom_ext (LinearMap.ext fun (y : k) ↦ ?_)
  have hy : (ModuleCat.Hom.hom
        (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) (c * (c⁻¹ * y)) =
      (ModuleCat.Hom.hom
        (e'.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) (c * (c⁻¹ * y)) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) (c⁻¹ * y)) hnat
  rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at hy

/-- **A morphism of line representations is determined by its scalar**, as soon as the
distinguished arrow acts invertibly or some other arrow exists. -/
theorem kroneckerLineRep_hom_ext (h : c ≠ 0 ∨ ∃ a : A, a ≠ a₁)
    {e e' : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d}
    (heq : kroneckerLineRepScalar e = kroneckerLineRepScalar e') : e = e' := by
  have hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : k) ↦ ?_)
    rw [kroneckerLineRep_hom_app_src_apply, kroneckerLineRep_hom_app_src_apply, heq]
  refine kroneckerRep_hom_ext hsrc ?_
  obtain hc | ⟨a, ha⟩ := h
  · exact app_tgt_ext_of_ne_zero hc hsrc
  · rw [kroneckerLineRep_hom_app_tgt_of_ne ha e, kroneckerLineRep_hom_app_tgt_of_ne ha e', hsrc]

private theorem kroneckerLineRepScalar_injective (h : c ≠ 0 ∨ ∃ a : A, a ≠ a₁) :
    Function.Injective
      (kroneckerLineRepScalar : (kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) → k) :=
  fun _ _ heq ↦ kroneckerLineRep_hom_ext h heq

/-- **The scalars of the two lines agree on the scalar of any morphism between them**, by
naturality along the distinguished arrow. -/
theorem kroneckerLineRepScalar_intertwine (h : a₀ ≠ a₁)
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    c * kroneckerLineRepScalar e = d * kroneckerLineRepScalar e := by
  have hnat := app_tgt_comp_mulLeft e
  rw [kroneckerLineRep_hom_app_tgt_of_ne h e] at hnat
  -- Reading the square at `1` gives the value of the component at `c`, which
  -- `TauCeti.kroneckerLineRep_hom_app_src_apply` computes on the other side.
  have h1 : (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom (c * 1 : k) =
      d * kroneckerLineRepScalar e :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) (1 : k)) hnat
  have h2 : (c * 1 : k) * kroneckerLineRepScalar e = d * kroneckerLineRepScalar e :=
    (kroneckerLineRep_hom_app_src_apply e (c * 1 : k)).symm.trans h1
  rwa [mul_one] at h2

/-- **Multiplication by `s` carries multiplication by `c` to multiplication by `d`** exactly when
`c * s = d * s`: the square along the distinguished arrow, stated on the base field, where the two
vertex spaces of a line representation are read. -/
private theorem mulLeft_comp_mulRight {s : k} (hs : c * s = d * s) :
    ModuleCat.ofHom (LinearMap.mulLeft k c) ≫ ModuleCat.ofHom (LinearMap.mulRight k s) =
      ModuleCat.ofHom (LinearMap.mulRight k s) ≫ ModuleCat.ofHom (LinearMap.mulLeft k d) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [mul_right_comm, hs, mul_assoc, mul_comm s x]

/-- **The morphism of line representations attached to an intertwining scalar**: multiplication by
`s` at both vertices. Every arrow other than the distinguished one acts by the identity on both
lines, so naturality there is automatic; along the distinguished one it says exactly that `s`
carries multiplication by `c` to multiplication by `d`. -/
noncomputable def kroneckerLineRepHom (s : k) (hs : c * s = d * s) :
    kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d :=
  kroneckerHom (ModuleCat.ofHom (LinearMap.mulRight k s))
    (ModuleCat.ofHom (LinearMap.mulRight k s)) fun a ↦ by
      by_cases ha : a = a₁
      · subst ha
        rw [kroneckerLineRep_map_arrowPath_self, kroneckerLineRep_map_arrowPath_self]
        exact mulLeft_comp_mulRight hs
      · rw [kroneckerLineRep_map_arrowPath_of_ne ha, kroneckerLineRep_map_arrowPath_of_ne ha]
        exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- At the source vertex, `TauCeti.kroneckerLineRepHom s hs` is multiplication by `s`. -/
@[simp]
theorem kroneckerLineRepHom_app_src (s : k) (hs : c * s = d * s) :
    (kroneckerLineRepHom (a₁ := a₁) (c := c) (d := d) s hs).app
        (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      ModuleCat.ofHom (LinearMap.mulRight k s) :=
  kroneckerHom_app_src _ _ _

/-- At the target vertex, `TauCeti.kroneckerLineRepHom s hs` is multiplication by `s`. -/
@[simp]
theorem kroneckerLineRepHom_app_tgt (s : k) (hs : c * s = d * s) :
    (kroneckerLineRepHom (a₁ := a₁) (c := c) (d := d) s hs).app
        (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      ModuleCat.ofHom (LinearMap.mulRight k s) :=
  kroneckerHom_app_tgt _ _ _

/-- The scalar of `TauCeti.kroneckerLineRepHom s hs` is `s`. -/
@[simp]
theorem kroneckerLineRepScalar_kroneckerLineRepHom (s : k) (hs : c * s = d * s) :
    kroneckerLineRepScalar (kroneckerLineRepHom (a₁ := a₁) (c := c) (d := d) s hs) = s := by
  have h : kroneckerLineRepScalar (kroneckerLineRepHom (a₁ := a₁) (c := c) (d := d) s hs) =
      1 * s :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) (1 : k))
      (kroneckerLineRepHom_app_src (a₁ := a₁) (c := c) (d := d) s hs)
  rw [h, one_mul]

-- Not `@[simp]`: the arrow `a₀` of the hypothesis does not occur in the left-hand side, which
-- `simpNF` rejects.
/-- **Every morphism of line representations is the one attached to its scalar.** Together with
`TauCeti.kroneckerLineRep_hom_ext` this identifies the morphisms `kroneckerLineRep k a₁ c ⟶
kroneckerLineRep k a₁ d`, on a quiver carrying an arrow other than the distinguished one, with the
scalars `s` satisfying `c * s = d * s`, mirroring the pair
`TauCeti.oneLoopRepHom_oneLoopRepScalar` / `TauCeti.oneLoopRep_hom_ext` of the loop quiver. -/
theorem kroneckerLineRepHom_kroneckerLineRepScalar (h : a₀ ≠ a₁)
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    kroneckerLineRepHom (kroneckerLineRepScalar e) (kroneckerLineRepScalar_intertwine h e) = e :=
  kroneckerLineRep_hom_ext (Or.inr ⟨a₀, h⟩) (kroneckerLineRepScalar_kroneckerLineRepHom _ _)

/-! ### Indecomposability and the classification -/

/-- **A line representation is indecomposable as soon as its scalar is nonzero or some arrow other
than the distinguished one exists.** Its endomorphisms are recorded faithfully by their scalar in
the base field, which is a local ring, so its only idempotent endomorphisms are `0` and the
identity.

What forces the two components of an endomorphism to agree is either an arrow other than the
distinguished one, acting as the identity on both, or the invertibility of the distinguished
arrow. The hypothesis is not an artefact: over the `A₂` quiver of a single arrow acting by `c = 0`
nothing relates the two components, and the line is there the direct sum of the two vertex
simples. That quiver has only the three isomorphism classes counted by
`TauCeti.card_skeleton_indecomposable_kronecker`, with no room for a family. -/
theorem indecomposable_kroneckerLineRep (h : c ≠ 0 ∨ ∃ a : A, a ≠ a₁) :
    Indecomposable (kroneckerLineRep k a₁ c) :=
  indecomposable_of_injective_of_isLocalRing not_isZero_kroneckerLineRep kroneckerLineRepScalar
    (kroneckerLineRepScalar_injective h) kroneckerLineRepScalar_zero kroneckerLineRepScalar_id
    fun e ↦ kroneckerLineRepScalar_comp e e

/-- **On a quiver carrying an arrow `a₀` other than the distinguished one, two isomorphic line
representations have equal scalars.** An isomorphism has an invertible scalar, and its naturality
along the distinguished arrow then equates the two scalars. The hypothesis `a₀ ≠ a₁` is essential:
on the `A₂` quiver of the single arrow `a₁` nothing forces the two components of a morphism to
agree, and the lines at any two nonzero scalars are isomorphic -- by the pair of multiplications
by `1` and by `d / c`. -/
theorem eq_of_nonempty_kroneckerLineRep_iso (h : a₀ ≠ a₁)
    (hiso : Nonempty (kroneckerLineRep k a₁ c ≅ kroneckerLineRep k a₁ d)) : c = d := by
  obtain ⟨e⟩ := hiso
  have hunit : kroneckerLineRepScalar e.hom * kroneckerLineRepScalar e.inv = 1 := by
    rw [← kroneckerLineRepScalar_comp, e.hom_inv_id, kroneckerLineRepScalar_id]
  exact mul_right_cancel₀ (left_ne_zero_of_mul_eq_one hunit)
    (kroneckerLineRepScalar_intertwine h e.hom)

/-- **Two line representations are isomorphic exactly when their scalars agree.** So over an
infinite field the isomorphism classes of indecomposables at the dimension vector `(1, 1)` are
infinite in number, the affine chart of the `ℙ¹` of the Kronecker quiver. -/
theorem nonempty_kroneckerLineRep_iso_iff (h : a₀ ≠ a₁) :
    Nonempty (kroneckerLineRep k a₁ c ≅ kroneckerLineRep k a₁ d) ↔ c = d :=
  ⟨eq_of_nonempty_kroneckerLineRep_iso h, by rintro rfl; exact ⟨Iso.refl _⟩⟩

/-- **On a generalized Kronecker quiver with two distinct arrows the dimension vector does not
determine an indecomposable.** Over every field such a quiver carries two non-isomorphic
finite-dimensional indecomposable representations with the same dimension vector, the lines at the
scalars `0` and `1`.

This is the sharpness of `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`:
that theorem holds over an acyclic quiver whose Tits form is positive definite, and the Kronecker
quiver is acyclic with a Tits form that is only positive semidefinite. -/
theorem exists_indecomposable_dimVector_eq_not_nonempty_iso_kronecker (k : Type u) [Field k]
    {A : Type v} {a₀ a₁ : A} (h : a₀ ≠ a₁) :
    ∃ M N : QuiverRep.{u, 0, v, u} k (Quiver.Kronecker A),
      IsFinDim k (Quiver.Kronecker A) M ∧ Indecomposable M ∧
        IsFinDim k (Quiver.Kronecker A) N ∧ Indecomposable N ∧
        dimVector M = dimVector N ∧ ¬ Nonempty (M ≅ N) :=
  ⟨kroneckerLineRep k a₁ 0, kroneckerLineRep k a₁ 1, isFinDim_kroneckerLineRep,
    indecomposable_kroneckerLineRep (Or.inr ⟨a₀, h⟩), isFinDim_kroneckerLineRep,
    indecomposable_kroneckerLineRep (Or.inr ⟨a₀, h⟩),
    funext fun w ↦ (dimVector_kroneckerLineRep w).trans (dimVector_kroneckerLineRep w).symm,
    fun hiso ↦ zero_ne_one (eq_of_nonempty_kroneckerLineRep_iso h hiso)⟩

/-- **The Tits value of the dimension vector of a line representation is `2 - #arrows`.** It is
`1` exactly for the `A₂` quiver of a single arrow, and `0` for the Kronecker quiver `• ⇉ •`.

This is the sharpness of `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`: over
an acyclic quiver whose Tits form is only positive semidefinite, the dimension vector of an
indecomposable need not have Tits value `1`, that is, need not be a *real* root. It remains a root
of the Kronecker quiver, an imaginary one: for two arrows `(1, 1)` is the isotropic null root of
`Ã₁` recorded by `TauCeti.Quiver.Kronecker.titsForm_eq_zero_iff_exists_smul`, and for more arrows
its Tits value `2 - #arrows` is negative. -/
theorem titsForm_dimVector_kroneckerLineRep [Fintype A] :
    titsForm (Quiver.Kronecker A)
        (fun j : Quiver.Kronecker A ↦ (dimVector (kroneckerLineRep k a₁ c) j : ℤ)) =
      2 - Fintype.card A := by
  have hd : (fun j : Quiver.Kronecker A ↦ (dimVector (kroneckerLineRep k a₁ c) j : ℤ)) = 1 := by
    funext j
    rw [dimVector_kroneckerLineRep, Nat.cast_one, Pi.one_apply]
  rw [hd]
  exact Quiver.Kronecker.titsForm_one

end TauCeti
