/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti.  Mathlib is not the destination (`ForTauCeti/README.md`);
what follows is where this material would have gone on the closed Mathlib track —
additions to `Mathlib/Analysis/RCLike/` (new file `ScalarTransport.lean`).

Formalized by Claude Opus 5 (claude-opus-5[1m]).

Transport of Hilbert-space structure along an isomorphism of `RCLike` fields.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic

/-! # Transport of a Hilbert space along an isomorphism of `RCLike` fields

`RCLike` is an open class, but it has exactly two models: `RCLike.I_eq_zero_or_im_I_eq_one`
says every `RCLike` field is isomorphic to `ℝ` or to `ℂ`.  A theorem proved at
those two fields is therefore true at every `RCLike` field — but only after the
statement has been carried across the isomorphism, and that is what this file
does.

The design is one transport, used twice.  `RCLikeIso 𝕜 𝕂` is a field isomorphism
fixing the reals and `I`; `RCLikeIso.real` and `RCLikeIso.complex` build the two
instances from Mathlib's `RCLike.realRingEquiv` and `RCLike.complexRingEquiv`.

`ScalarTransport e E` is `E` with the `𝕂`-structure its `𝕜`-structure induces
through `e`.  The type, the additive group, the topology and the **norm** are
unchanged; only the scalar action and the field the inner product takes values in
move.  So most of what follows is a bijection between two spellings of the same
object, and the transported object is equal to the original wherever that makes
sense:

| object | transport | preserved |
| --- | --- | --- |
| `Submodule 𝕜 E` | `ScalarTransport.submodule` | the carrier, `ᗮ`, `Module.rank` |
| `E →L[𝕜] F` | `ScalarTransport.clm` | the function, `‖·‖`, `adjoint`, `IsSelfAdjoint` |
| `Submodule.starProjection` | — | it *is* the transported projection |
| `E →ₗ.[𝕜] F` | `ScalarTransport.pmap` | the domain, the function, `adjoint`, `IsSelfAdjoint` |

Nothing here is specific to any application: it is the general statement that a
Hilbert space over an `RCLike` field is a Hilbert space over `ℝ` or `ℂ`, in a way
that carries the operator theory with it.

## Why not restriction of scalars

`InnerProductSpace.rclikeToReal` restricts a `𝕜`-space to `ℝ`.  That is a
different construction and it does not answer this question: over a complex-like
`𝕜` it halves the scalars, doubling `Module.rank` and changing the singular-value
sequence of an operator.  The transport here changes no ranks, because it changes
no scalars — it renames the field.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  Written directly here, 2026-09-01, because the Palomar
  Section 2 Challenge needs its four theorems at an arbitrary `RCLike` field and
  the development's endpoints are stated at `ℝ` and `ℂ`.
* Extraction class: **new**.  It depends on nothing outside Mathlib, and is the
  reason the two capability classes
  `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` and
  `TauCeti.DavisKahan.Sylvester.HasUnboundedSylvesterKyFan` stopped being
  hypotheses.
* Namespace: `TauCeti`, per `ForTauCeti/README.md` section 2.
* `@[expose]` on ten definitional carriers, each measured load-bearing by
  deleting the attribute and reading the compiler's complaint.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

public section

open scoped InnerProductSpace

universe u w v v'

namespace TauCeti

/-- An isomorphism of `RCLike` fields fixing the reals and `I`. -/
structure RCLikeIso (𝕜 : Type u) (𝕂 : Type w) [RCLike 𝕜] [RCLike 𝕂] where
  toRingEquiv : 𝕜 ≃+* 𝕂
  map_ofReal : ∀ r : ℝ, toRingEquiv (r : 𝕜) = (r : 𝕂)
  map_I : toRingEquiv (RCLike.I : 𝕜) = RCLike.I

namespace RCLikeIso

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]

/-- The isomorphism acts as a function. -/
instance : CoeFun (RCLikeIso 𝕜 𝕂) (fun _ => 𝕜 → 𝕂) := ⟨fun e => e.toRingEquiv⟩

/-- The coercion to a function is the underlying ring equivalence. -/
@[simp] theorem coe_toRingEquiv (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : e.toRingEquiv x = e x := rfl

/-- Reverse an isomorphism of `RCLike` fields. -/
def symm (e : RCLikeIso 𝕜 𝕂) : RCLikeIso 𝕂 𝕜 where
  toRingEquiv := e.toRingEquiv.symm
  map_ofReal r := by
    apply e.toRingEquiv.injective
    simp only [RingEquiv.apply_symm_apply, e.map_ofReal]
  map_I := by
    apply e.toRingEquiv.injective
    simp only [RingEquiv.apply_symm_apply, e.map_I]

/-- When `I = 0` the field is `ℝ`. -/
noncomputable def real (h : (RCLike.I : 𝕜) = 0) : RCLikeIso 𝕜 ℝ where
  toRingEquiv := RCLike.realRingEquiv h
  map_ofReal r := by simp
  map_I := by simp [h]

/-- When `im I = 1` the field is `ℂ`. -/
noncomputable def complex (h : RCLike.im (RCLike.I : 𝕜) = 1) : RCLikeIso 𝕜 ℂ where
  toRingEquiv := RCLike.complexRingEquiv h
  map_ofReal r := by simp
  map_I := by simp [h]

/-- The isomorphism is determined by its action on the real and imaginary parts. -/
theorem apply_eq (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) :
    e x = (RCLike.re x : 𝕂) + (RCLike.im x : 𝕂) * RCLike.I := by
  conv_lhs => rw [← RCLike.re_add_im x]
  rw [map_add, map_mul, e.map_ofReal, e.map_ofReal, e.map_I]

/-- The isomorphism preserves real parts. -/
@[simp] theorem re_map (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : RCLike.re (e x) = RCLike.re x := by
  rw [apply_eq]; simp

/-- `I` vanishes on one side exactly when it vanishes on the other. -/
theorem im_I_map (e : RCLikeIso 𝕜 𝕂) :
    RCLike.im (RCLike.I : 𝕂) = RCLike.im (RCLike.I : 𝕜) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · have : (RCLike.I : 𝕂) = 0 := by rw [← e.map_I, h, map_zero]
    simp [this, h]
  · have : (RCLike.I : 𝕂) ≠ 0 := by
      rw [← e.map_I]
      simpa using fun hc => by simp [hc] at h
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕂) with h' | h'
    · exact absurd h' this
    · rw [h, h']

/-- The isomorphism preserves imaginary parts. -/
@[simp] theorem im_map (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : RCLike.im (e x) = RCLike.im x := by
  rw [apply_eq]; simp [e.im_I_map]

/-- The isomorphism preserves norms. -/
@[simp] theorem norm_map (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) : ‖e x‖ = ‖x‖ := by
  have h1 : ‖e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def, e.re_map, e.im_map]
  nlinarith [norm_nonneg (e x), norm_nonneg x, h1]

/-- The isomorphism commutes with conjugation. -/
@[simp] theorem map_conj (e : RCLikeIso 𝕜 𝕂) (x : 𝕜) :
    e (starRingEnd 𝕜 x) = starRingEnd 𝕂 (e x) := by
  rw [apply_eq, apply_eq]; simp [RCLike.conj_re, RCLike.conj_im]

/-- The inverse preserves norms. -/
@[simp] theorem norm_symm_map' (e : RCLikeIso 𝕜 𝕂) (c : 𝕂) :
    ‖e.toRingEquiv.symm c‖ = ‖c‖ := by
  conv_rhs => rw [← e.toRingEquiv.apply_symm_apply c]
  exact (e.norm_map _).symm

/-- The isomorphism is an isometry. -/
theorem isometry (e : RCLikeIso 𝕜 𝕂) : Isometry (e : 𝕜 → 𝕂) :=
  AddMonoidHomClass.isometry_of_norm (e.toRingEquiv : 𝕜 →+* 𝕂) e.norm_map

/-- The field isomorphism is a homeomorphism. -/
@[expose]
noncomputable def homeomorph (e : RCLikeIso 𝕜 𝕂) : 𝕜 ≃ₜ 𝕂 where
  toEquiv := e.toRingEquiv.toEquiv
  continuous_toFun := e.isometry.continuous
  continuous_invFun := by
    refine (AddMonoidHomClass.isometry_of_norm
      (e.toRingEquiv.symm : 𝕂 →+* 𝕜) fun c => ?_).continuous
    exact e.norm_symm_map' c

/-- The homeomorphism is the isomorphism. -/
@[simp] theorem coe_homeomorph (e : RCLikeIso 𝕜 𝕂) : (e.homeomorph : 𝕜 → 𝕂) = e := rfl

/-- The inverse preserves norms. -/
@[simp] theorem norm_symm_map (e : RCLikeIso 𝕜 𝕂) (c : 𝕂) :
    ‖e.toRingEquiv.symm c‖ = ‖c‖ := by
  conv_rhs => rw [← e.toRingEquiv.apply_symm_apply c]
  exact (e.norm_map _).symm

end RCLikeIso

/-- `E`, carrying the `𝕂`-Hilbert structure its `𝕜`-structure induces through `e`.

The type, the additive group, the topology and the norm are unchanged; only the
scalar action and the inner product's field of values move. -/
@[expose, nolint unusedArguments]
def ScalarTransport {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]
    (_e : RCLikeIso 𝕜 𝕂) (E : Type v) : Type v := E

namespace ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type v'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The identity, as the passage from `E` to its transport. -/
@[expose]
def of (x : E) : ScalarTransport e E := x

/-- The identity, as the passage back. -/
@[expose]
def out (x : ScalarTransport e E) : E := x

omit [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in
/-- `of` and `out` are mutually inverse. -/
@[simp] theorem of_out (x : ScalarTransport e E) : of (e := e) (out x) = x := rfl
omit [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in
/-- `of` and `out` are mutually inverse. -/
@[simp] theorem out_of (x : E) : out (of (e := e) x) = x := rfl

/-- The transport does not touch the additive normed structure. -/
instance : NormedAddCommGroup (ScalarTransport e E) := inferInstanceAs (NormedAddCommGroup E)

/-- Scalars act through `e⁻¹`. -/
instance : Module 𝕂 (ScalarTransport e E) :=
  Module.compHom E (e.toRingEquiv.symm : 𝕂 →+* 𝕜)

/-- Scalars act through `e⁻¹`. -/
theorem smul_def (c : 𝕂) (x : ScalarTransport e E) :
    c • x = of (e := e) ((e.toRingEquiv.symm c) • out x) := rfl

/-- and isometrically, because `e` is. -/
noncomputable instance : NormedSpace 𝕂 (ScalarTransport e E) where
  norm_smul_le c x := by
    change ‖(e.toRingEquiv.symm c) • (out x)‖ ≤ ‖c‖ * ‖x‖
    rw [norm_smul, e.norm_symm_map]
    rfl

/-- The inner product is the original, carried across `e`. -/
noncomputable instance : InnerProductSpace 𝕂 (ScalarTransport e E) where
  inner x y := e (inner 𝕜 (out x) (out y))
  norm_sq_eq_re_inner x := by
    change ‖out x‖ ^ 2 = RCLike.re (e (inner 𝕜 (out x) (out x)))
    rw [e.re_map]; exact norm_sq_eq_re_inner (𝕜 := 𝕜) _
  conj_inner_symm x y := by
    rw [← e.map_conj, inner_conj_symm]
  add_left x y z := by
    change e (inner 𝕜 (out x + out y) (out z)) =
      e (inner 𝕜 (out x) (out z)) + e (inner 𝕜 (out y) (out z))
    rw [inner_add_left, map_add]
  smul_left x y r := by
    change e (inner 𝕜 ((e.toRingEquiv.symm r) • out x) (out y)) =
      starRingEnd 𝕂 r * e (inner 𝕜 (out x) (out y))
    rw [inner_smul_left, map_mul, e.map_conj, e.toRingEquiv.apply_symm_apply]

/-- Completeness is a fact about the metric, which is unchanged. -/
instance [CompleteSpace E] : CompleteSpace (ScalarTransport e E) :=
  inferInstanceAs (CompleteSpace E)

omit [InnerProductSpace 𝕜 E] in
/-- The transport does not change the norm. -/
@[simp] theorem norm_of (x : E) : ‖of (e := e) x‖ = ‖x‖ := rfl

/-- The transported inner product is the original, carried across `e`. -/
@[simp] theorem inner_of (x y : E) :
    inner 𝕂 (of (e := e) x) (of (e := e) y) = e (inner 𝕜 x y) := rfl

/-- A real scalar acts the same on both sides. -/
@[simp] theorem ofReal_smul_of (r : ℝ) (x : E) :
    ((r : 𝕂)) • of (e := e) x = of (e := e) ((r : 𝕜) • x) := by
  rw [smul_def]
  have : e.toRingEquiv.symm ((r : 𝕂)) = ((r : 𝕜)) := by
    rw [← e.map_ofReal r]
    exact e.toRingEquiv.symm_apply_apply _
  rw [this]
  rfl

/-- and its real part is literally unchanged. -/
@[simp] theorem re_inner_of (x y : E) :
    RCLike.re (inner 𝕂 (of (e := e) x) (of (e := e) y)) = RCLike.re (inner 𝕜 x y) := by
  rw [inner_of, e.re_map]

/-! ### Subspaces -/

/-- A `𝕜`-subspace of `E`, as a `𝕂`-subspace of the transport, with the same carrier. -/
@[expose]
def submodule (S : Submodule 𝕜 E) : Submodule 𝕂 (ScalarTransport e E) where
  carrier := {x | out x ∈ S}
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' _ _ hx := S.smul_mem _ hx

/-- Membership in a transported subspace is membership in the original. -/
@[simp] theorem mem_submodule {S : Submodule 𝕜 E} {x : ScalarTransport e E} :
    x ∈ submodule (e := e) S ↔ out x ∈ S := Iff.rfl

/-- and back again. -/
@[expose]
def submoduleSymm (S : Submodule 𝕂 (ScalarTransport e E)) : Submodule 𝕜 E where
  carrier := {x | of (e := e) x ∈ S}
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c x hx := by
    have : (e c) • (of (e := e) x) ∈ S := S.smul_mem _ hx
    rwa [smul_def, e.toRingEquiv.symm_apply_apply] at this

/-- Membership in a subspace read back is membership in the original. -/
@[simp] theorem mem_submoduleSymm {S : Submodule 𝕂 (ScalarTransport e E)} {x : E} :
    x ∈ submoduleSymm S ↔ of (e := e) x ∈ S := Iff.rfl

/-- The two directions are mutually inverse. -/
@[simp] theorem submoduleSymm_submodule (S : Submodule 𝕜 E) :
    submoduleSymm (submodule (e := e) S) = S := rfl

/-- The two directions are mutually inverse. -/
@[simp] theorem submodule_submoduleSymm (S : Submodule 𝕂 (ScalarTransport e E)) :
    submodule (e := e) (submoduleSymm S) = S := rfl

/-- The transport preserves orthogonal complements. -/
@[simp] theorem submodule_orthogonal (S : Submodule 𝕜 E) :
    (submodule (e := e) S)ᗮ = submodule (e := e) Sᗮ := by
  ext x
  simp only [Submodule.mem_orthogonal, mem_submodule]
  constructor
  · intro h y hy
    have h2 : inner 𝕂 (of (e := e) y) x = 0 := h (of (e := e) y) hy
    have h3 : e (inner 𝕜 y (out x)) = 0 := h2
    simpa using congrArg e.toRingEquiv.symm h3
  · intro h y hy
    have h2 : inner 𝕜 (out y) (out x) = 0 := h (out y) hy
    change e (inner 𝕜 (out y) (out x)) = 0
    rw [h2, map_zero]

/-! ### Bounded operators -/

/-- A `𝕜`-linear continuous map, as a `𝕂`-linear one on the transports. -/
@[expose]
def clm (T : E →L[𝕜] F) : ScalarTransport e E →L[𝕂] ScalarTransport e F where
  toFun x := of (e := e) (T (out x))
  map_add' _ _ := T.map_add _ _
  map_smul' _ _ := T.map_smul _ _
  cont := T.continuous

/-- The transported operator is the original function. -/
@[simp] theorem clm_apply (T : E →L[𝕜] F) (x : E) :
    clm (e := e) T (of x) = of (T x) := rfl

/-- The transport of operators is subtractive: it does not change the functions. -/
@[simp] theorem clm_sub (T R : E →L[𝕜] F) :
    clm (e := e) (T - R) = clm (e := e) T - clm (e := e) R := rfl

/-- and has the same operator norm. -/
@[simp] theorem clm_norm (T : E →L[𝕜] F) : ‖clm (e := e) T‖ = ‖T‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
  · exact T.le_opNorm (out x)
  · exact (clm (e := e) T).le_opNorm (of x)

/-- The transport of a bounded operator is a bijection onto the `𝕂`-operators. -/
@[expose]
def clmEquiv : (E →L[𝕜] F) ≃ (ScalarTransport e E →L[𝕂] ScalarTransport e F) where
  toFun := clm
  invFun T :=
    { toFun := fun x => out (T (of (e := e) x))
      map_add' := fun _ _ => T.map_add _ _
      map_smul' := fun c x => by
        have h := T.map_smul (e c) (of (e := e) x)
        rw [smul_def, e.toRingEquiv.symm_apply_apply] at h
        change out (T (of (e := e) (c • x))) = c • out (T (of (e := e) x))
        rw [show of (e := e) (c • x) = of (e := e) (c • out (of (e := e) x)) from rfl, h,
          smul_def, e.toRingEquiv.symm_apply_apply]
        rfl
      cont := T.continuous }
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Rank -/

/-- The additive identity `E ≃+ ScalarTransport e E`. -/
@[expose]
def addEquiv : E ≃+ ScalarTransport e E where
  toFun := of
  invFun := out
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The additive identity intertwines the two scalar actions through `e`. -/
theorem addEquiv_smul (r : 𝕜) (x : E) :
    addEquiv (e := e) (r • x) = e r • addEquiv (e := e) x := by
  change of (e := e) (r • x) = e r • of (e := e) x
  rw [smul_def, e.toRingEquiv.symm_apply_apply]
  rfl

/-- Rank is unchanged by the transport: the scalar action is the same up to `e`. -/
theorem rank_eq (S : Submodule 𝕜 E) :
    Module.rank 𝕜 S = Module.rank 𝕂 (submodule (e := e) S) :=
  rank_eq_of_equiv_equiv (R := 𝕜) (R' := 𝕂) (M := S) (M₁ := submodule (e := e) S)
    (fun r => e r)
    { toFun := fun x => ⟨of (e := e) (x : E), x.2⟩
      invFun := fun x => ⟨out (x : ScalarTransport e E), x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
    e.toRingEquiv.bijective
    (fun r m => Subtype.ext (addEquiv_smul (e := e) r (m : E)))

/-- Hence the rank of a transported map. -/
theorem rank_clm_eq (T : E →L[𝕜] F) :
    LinearMap.rank ((clm (e := e) T : ScalarTransport e E →L[𝕂] ScalarTransport e F) :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e F) =
      LinearMap.rank (T : E →ₗ[𝕜] F) := by
  have hrange : LinearMap.range
      ((clm (e := e) T : ScalarTransport e E →L[𝕂] ScalarTransport e F) :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e F) =
      submodule (e := e) (LinearMap.range (T : E →ₗ[𝕜] F)) := by
    ext y
    simp only [LinearMap.mem_range, mem_submodule]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨out x, rfl⟩
    · rintro ⟨x, hx⟩; exact ⟨of (e := e) x, congrArg (of (e := e)) hx⟩
  rw [LinearMap.rank, LinearMap.rank, hrange, ← rank_eq]

/-! ### Orthogonal projections -/

/-- A transported subspace inherits its orthogonal projection. -/
instance hasOrthogonalProjection (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    (submodule (e := e) S).HasOrthogonalProjection where
  exists_orthogonal x := by
    obtain ⟨w, hw, hsub⟩ :=
      Submodule.HasOrthogonalProjection.exists_orthogonal (K := S) (out x)
    exact ⟨of (e := e) w, hw, by rw [submodule_orthogonal]; exact hsub⟩

/-- and the projection is the original projection. -/
@[simp] theorem starProjection_of (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] (x : E) :
    (submodule (e := e) S).starProjection (of (e := e) x) = of (e := e) (S.starProjection x) := by
  have hmem : S.starProjection x ∈ S := S.starProjection_apply_mem x
  have hperp : x - S.starProjection x ∈ Sᗮ := S.sub_starProjection_mem_orthogonal x
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := submodule (e := e) S)
    (u := of (e := e) x) (v := of (e := e) (S.starProjection x)) hmem fun w hw => ?_
  change e (inner 𝕜 (out (of (e := e) x - of (e := e) (S.starProjection x))) (out w)) = 0
  rw [show out (of (e := e) x - of (e := e) (S.starProjection x)) = x - S.starProjection x from rfl,
    show inner 𝕜 (x - S.starProjection x) (out w) = 0 from
      (Submodule.mem_orthogonal' _ _).mp hperp (out w) hw, map_zero]

/-- The transported projection is the transport of the projection. -/
@[simp] theorem starProjection_clm (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    (submodule (e := e) S).starProjection = clm (e := e) S.starProjection := by
  ext x
  exact starProjection_of (e := e) S (out x)

/-! ### Adjoints -/

variable [CompleteSpace E] [CompleteSpace F]

/-- The adjoint of a transported operator is the transport of its adjoint. -/
@[simp] theorem adjoint_clm (T : E →L[𝕜] F) :
    ContinuousLinearMap.adjoint (clm (e := e) T) =
      clm (e := e) (ContinuousLinearMap.adjoint T) := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left 𝕂 fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  change e (inner 𝕜 (T (out x)) (out y)) = e (inner 𝕜 (out x) (T.adjoint (out y)))
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- Self-adjointness is preserved and reflected by the transport. -/
theorem isSelfAdjoint_clm_iff {T : E →L[𝕜] E} :
    IsSelfAdjoint (clm (e := e) T) ↔ IsSelfAdjoint T := by
  constructor
  · intro h
    have hc := adjoint_clm (e := e) T
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp h] at hc
    refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
    have : clm (e := e) (ContinuousLinearMap.adjoint T) = clm (e := e) T := hc.symm
    exact (clmEquiv (e := e)).injective this
  · intro h
    refine ContinuousLinearMap.isSelfAdjoint_iff'.mpr ?_
    rw [adjoint_clm, ContinuousLinearMap.isSelfAdjoint_iff'.mp h]

/-! ### Partial maps -/

/-- A point of the transported domain, read back in `A.domain`. -/
@[expose]
def domainOut (A : E →ₗ.[𝕜] F) (x : submodule (e := e) A.domain) : A.domain :=
  ⟨out (x : ScalarTransport e E), x.2⟩

/-- A `𝕜`-linear partial map, as a `𝕂`-linear one on the transports:
the same domain and the same function. -/
@[expose]
def pmap (A : E →ₗ.[𝕜] F) : ScalarTransport e E →ₗ.[𝕂] ScalarTransport e F where
  domain := submodule (e := e) A.domain
  toFun :=
    { toFun := fun x => of (e := e) (A (domainOut (e := e) A x))
      map_add' := fun x y => congrArg (of (e := e)) (A.map_add _ _)
      map_smul' := fun c x => by
        have hd : domainOut (e := e) A (c • x) =
            (e.toRingEquiv.symm c) • domainOut (e := e) A x := rfl
        change of (e := e) (A (domainOut (e := e) A (c • x))) =
          c • of (e := e) (A (domainOut (e := e) A x))
        rw [hd, A.map_smul, smul_def]
        rfl }

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transported partial map has the transported domain. -/
@[simp] theorem pmap_domain (A : E →ₗ.[𝕜] F) :
    (pmap (e := e) A).domain = submodule (e := e) A.domain := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- and the original function. -/
@[simp] theorem pmap_apply (A : E →ₗ.[𝕜] F) (x : (pmap (e := e) A).domain) :
    pmap (e := e) A x = of (e := e) (A (domainOut (e := e) A x)) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Density of the domain is unchanged: the carrier and the topology are. -/
theorem dense_pmap_domain_iff (A : E →ₗ.[𝕜] F) :
    Dense ((pmap (e := e) A).domain : Set (ScalarTransport e E)) ↔
      Dense (A.domain : Set E) := Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transported adjoint domain is the original one, because `e` is a homeomorphism. -/
theorem mem_pmap_adjointDomain_iff (A : E →ₗ.[𝕜] F) (y : ScalarTransport e F) :
    y ∈ (pmap (e := e) A).adjointDomain ↔ out y ∈ A.adjointDomain := by
  change Continuous (fun x : (pmap (e := e) A).domain =>
      inner 𝕂 y ((pmap (e := e) A) x)) ↔
    Continuous (fun x : A.domain => inner 𝕜 (out y) (A x))
  rw [← e.homeomorph.comp_continuous_iff]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transported adjoint domain is the transport of the adjoint domain. -/
@[simp] theorem pmap_adjointDomain (A : E →ₗ.[𝕜] F) :
    (pmap (e := e) A).adjointDomain = submodule (e := e) A.adjointDomain :=
  SetLike.ext fun y => mem_pmap_adjointDomain_iff (e := e) A y

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transport of partial maps is injective. -/
theorem pmap_injective : Function.Injective (pmap (e := e) (E := E) (F := F)) := by
  intro A B h
  have hdom : A.domain = B.domain := by
    have h0 := congrArg LinearPMap.domain h
    have := congrArg (submoduleSymm (e := e)) h0
    rwa [pmap_domain, pmap_domain, submoduleSymm_submodule, submoduleSymm_submodule] at this
  refine LinearPMap.ext hdom fun x hA hB => ?_
  have := LinearPMap.ext_iff.mp h
  obtain ⟨_, hval⟩ := this
  exact hval (x := of (e := e) x) (hf := hA) (hg := hB)

omit [CompleteSpace F] in
variable (e) in
/-- The adjoint of a transported partial map is the transport of its adjoint. -/
theorem pmap_adjoint (A : E →ₗ.[𝕜] F) (hA : Dense (A.domain : Set E)) :
    (pmap (e := e) A).adjoint = pmap (e := e) A.adjoint := by
  have hA' : Dense ((pmap (e := e) A).domain : Set (ScalarTransport e E)) := hA
  refine LinearPMap.ext (by simp [LinearPMap.adjoint]) fun y hf hg => ?_
  refine LinearPMap.adjoint_apply_eq hA' ⟨y, hf⟩ (x₀ := of (e := e) (A.adjoint ⟨out y, hg⟩))
    fun x => ?_
  change e (inner 𝕜 (A.adjoint ⟨out y, hg⟩) (out ((x : ScalarTransport e E)))) =
    e (inner 𝕜 (out y) (A (domainOut (e := e) A x)))
  exact congrArg e.toRingEquiv (LinearPMap.adjoint_isFormalAdjoint hA ⟨out y, hg⟩ _)

variable (e) in
/-- Self-adjointness is preserved and reflected by the transport. -/
theorem isSelfAdjoint_pmap_iff {A : E →ₗ.[𝕜] E} :
    IsSelfAdjoint (pmap (e := e) A) ↔ IsSelfAdjoint A := by
  constructor
  · intro h
    have hdense : Dense (A.domain : Set E) := h.dense_domain
    have := LinearPMap.isSelfAdjoint_def.mp h
    rw [pmap_adjoint e A hdense] at this
    exact LinearPMap.isSelfAdjoint_def.mpr (pmap_injective (e := e) this)
  · intro h
    refine LinearPMap.isSelfAdjoint_def.mpr ?_
    rw [pmap_adjoint e A h.dense_domain, LinearPMap.isSelfAdjoint_def.mp h]

end ScalarTransport

end TauCeti
