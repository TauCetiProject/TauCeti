/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.RCLike.ScalarTransport

/-!
# Linear isometric equivalences survive a change of scalar field

An isometry between two Hilbert spaces over `𝕜` is an isometry between their
transports over `𝕂`: the function, the addition and the norm are unchanged, and
the scalar action moves along `e` by `TauCeti.ScalarTransport.smul_def`.

The statement that two subspaces are isometrically isomorphic — Davis and Kahan's
standing condition (3.5), for instance — therefore does not see the scalar field.

## Main results

* `TauCeti.ScalarTransport.linearIsometryEquiv`.
* `TauCeti.ScalarTransport.submoduleEquivOfEq`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

public section

namespace TauCeti
namespace ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {X Y : Type v}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- **A linear isometric equivalence transports.** -/
noncomputable def linearIsometryEquiv (f : X ≃ₗᵢ[𝕜] Y) :
    ScalarTransport e X ≃ₗᵢ[𝕂] ScalarTransport e Y where
  toFun x := of (e := e) (f (out (e := e) x))
  invFun y := of (e := e) (f.symm (out (e := e) y))
  left_inv x := by
    change of (e := e) (f.symm (f (out (e := e) x))) = x
    rw [f.symm_apply_apply, of_out]
  right_inv y := by
    change of (e := e) (f (f.symm (out (e := e) y))) = y
    rw [f.apply_symm_apply, of_out]
  map_add' x y := by
    change of (e := e) (f (out (e := e) x + out (e := e) y)) =
      of (e := e) (f (out (e := e) x)) + of (e := e) (f (out (e := e) y))
    rw [map_add]
    rfl
  map_smul' c x := by
    change of (e := e) (f (e.toRingEquiv.symm c • out (e := e) x)) =
      c • of (e := e) (f (out (e := e) x))
    rw [map_smul, smul_def]
    rfl
  norm_map' x := f.norm_map _

/-- The transport commutes with intersection of subspaces. -/
theorem submodule_inf (S T : Submodule 𝕜 X) :
    submodule (e := e) (S ⊓ T) =
      submodule (e := e) S ⊓ submodule (e := e) T := by
  ext x
  simp only [mem_submodule, Submodule.mem_inf]

/-- **The subtype of a transported subspace is the transport of the original subtype.**

`ScalarTransport.submodule S` keeps exactly the carrier of `S`, while
`ScalarTransport e S` transports the Hilbert structure on the subtype itself.
This canonical isometry is the adapter between those two spellings.  It is the
missing coordinate map needed to transport partial operators whose domain or
codomain is a closed subspace, such as an unbounded Ritz compression. -/
@[expose]
noncomputable def submoduleSubtypeEquiv (S : Submodule 𝕜 X) :
    ScalarTransport e S ≃ₗᵢ[𝕂] (submodule (e := e) S : Submodule 𝕂 (ScalarTransport e X)) where
  toFun x := ⟨of (e := e) ((out (e := e) x : S) : X), (out (e := e) x : S).2⟩
  invFun y := of (e := e) (⟨out (e := e) (y : ScalarTransport e X), y.2⟩ : S)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- **The transport of an orthogonal-complement subtype is canonically the
orthogonal complement of the transported subspace.**

This is the codomain adapter needed by directed tangent corners.  Keeping it as
an isometric equivalence avoids exposing equality casts between
`submodule (Sᗮ)` and `(submodule S)ᗮ` to downstream APIs. -/
noncomputable def orthogonalSubmoduleSubtypeEquiv (S : Submodule 𝕜 X) :
    ScalarTransport e Sᗮ ≃ₗᵢ[𝕂]
      ((submodule (e := e) S)ᗮ : Submodule 𝕂 (ScalarTransport e X)) := by
  rw [submodule_orthogonal]
  exact submoduleSubtypeEquiv (e := e) Sᗮ

/-- The transported-subspace adapter does not move the ambient vector. -/
@[simp] theorem submoduleSubtypeEquiv_coe_apply (S : Submodule 𝕜 X)
    (x : ScalarTransport e S) :
    (((submoduleSubtypeEquiv (e := e) S x :
        submodule (e := e) S) : ScalarTransport e X)) =
      of (e := e) (((out (e := e) x : S) : X)) := rfl

/-- Nor does its inverse move the ambient vector. -/
@[simp] theorem submoduleSubtypeEquiv_symm_coe_apply (S : Submodule 𝕜 X)
    (x : submodule (e := e) S) :
    out (e := e) ((submoduleSubtypeEquiv (e := e) S).symm x) =
      (⟨out (e := e) (x : ScalarTransport e X), x.2⟩ : S) := rfl

/-- Two subspaces with the same carrier give isometric coercions. -/
noncomputable def submoduleEquivOfEq {S T : Submodule 𝕜 X} (h : S = T) :
    (S : Submodule 𝕜 X) ≃ₗᵢ[𝕜] (T : Submodule 𝕜 X) where
  toFun x := ⟨(x : X), h ▸ x.2⟩
  invFun y := ⟨(y : X), h ▸ y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end ScalarTransport
end TauCeti
