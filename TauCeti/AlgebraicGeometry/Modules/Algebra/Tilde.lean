/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality

/-!
# Module maps from `M~` to a function algebra

For a commutative ring `R`, an `R`-module `M` and a scheme `q : T ⟶ Spec R`, module maps
`M~ ⟶ q_* 𝒪_T` from the associated sheaf of `M` to the function algebra of `q` are the `R`-linear
maps `M → Γ(T, ⊤)`, where `R` acts on `Γ(T, ⊤)` through `R ≅ Γ(Spec R, ⊤) ⟶ Γ(T, ⊤)`
(`AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv`). This is Mathlib's adjunction
`AlgebraicGeometry.tilde.adjunction` between `~` and global sections, followed by the
identification `Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv` of global sections of `q_* 𝒪_T`
with global functions on `T`. The description is natural in `T`
(`AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv_comp`).

It is the analogue for `M~` of `AlgebraicGeometry.Scheme.Hom.freeHomPushforwardEquiv`, which
describes module maps out of a free sheaf, and it computes the points of relative spectra of
symmetric algebras over an affine base.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_smul`: the `R`-module
  structure of `Γ(q_* 𝒪_T, ⊤)` is multiplication by the image of `R` in `Γ(T, ⊤)`;
* `AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv`: module maps `M~ ⟶ q_* 𝒪_T` are the
  `R`-linear maps `M → Γ(T, ⊤)`;
* `AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv_comp`: naturality in `T`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {R : CommRingCat.{u}} {T : Scheme.{u}}

/-- Under the identification of global sections of `q_* 𝒪_T` with global functions on `T`, the
`R`-module structure of `Γ(q_* 𝒪_T, ⊤)` is multiplication through `R ≅ Γ(Spec R, ⊤) ⟶ Γ(T, ⊤)`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_smul
    (q : T ⟶ Spec R) (r : R)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ T.Modules))) :
    q.pushforwardStructureAlgebraΓRingEquiv.symm (r • x) =
      ((Scheme.ΓSpecIso R).inv ≫ q.appTop) r * q.pushforwardStructureAlgebraΓRingEquiv.symm x := by
  -- By definition of `moduleSpecΓFunctor` and of the pushforward, `r` acts on
  -- `Γ(q_* 𝒪_T, ⊤) = Γ(T, q⁻¹ ⊤)` as multiplication by `q^♯` of the restriction of `r` from `⊤`
  -- to `⊤`; this is stated with `show` because the two module structures are only definitionally
  -- equal.
  have h : (r • x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ T.Modules))) =
      ((show Γ(T, q ⁻¹ᵁ ⊤) from q.app ⊤ ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
        ((Scheme.ΓSpecIso R).inv r))) * (show Γ(T, q ⁻¹ᵁ ⊤) from x) : Γ(T, q ⁻¹ᵁ ⊤)) := rfl
  have h₁ : (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
  have h₂ : (homOfLE (by simp : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤)).op = 𝟙 (op (q ⁻¹ᵁ ⊤)) :=
    Subsingleton.elim _ _
  rw [h₁, (Spec R).presheaf.map_id] at h
  rw [h]
  -- The section-ring identifications are restrictions along `⊤ ≤ q⁻¹ ⊤`, the identity. Their
  -- arguments are typed in `moduleSpecΓFunctor.obj _`, so the rewrites need `erw`.
  erw [Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_apply,
    Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_apply,
    Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply,
    Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply]
  rw [h₂]
  erw [T.presheaf.map_id]
  rfl

/-- Module maps from the sheaf `M~` on `Spec R` to the function algebra `q_* 𝒪_T` of
`q : T ⟶ Spec R` are the `R`-linear maps `M → Γ(T, ⊤)`, where `R` acts on `Γ(T, ⊤)` through
`R ≅ Γ(Spec R, ⊤) ⟶ Γ(T, ⊤)`. It is the adjunction between `~` and global sections, followed by the
identification of global sections of `q_* 𝒪_T` with global functions on `T`. -/
def _root_.AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv (q : T ⟶ Spec R)
    (M : ModuleCat.{u} R) :
    (tilde M ⟶ (Scheme.Modules.pushforward q).obj (𝟙_ T.Modules)) ≃
      (M →ₛₗ[((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom] Γ(T, ⊤)) :=
  (tilde.adjunction.homEquiv _ _).trans
    { toFun f :=
        { toFun m := q.pushforwardStructureAlgebraΓRingEquiv.symm (f m)
          map_add' m n := by rw [map_add]; exact map_add _ _ _
          map_smul' r m := by
            rw [map_smul]; exact q.pushforwardStructureAlgebraΓRingEquiv_symm_smul r (f m) }
      -- The `show` and the explicit target give the linear map the `R`-module structure of
      -- `moduleSpecΓFunctor.obj _`, which elaboration does not find on its carrier.
      invFun g :=
        show M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ T.Modules)) from
          ModuleCat.ofHom (X := M)
            (Y := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ T.Modules)))
          { toFun m := q.pushforwardStructureAlgebraΓRingEquiv (g m)
            map_add' m n := by rw [map_add]; exact map_add _ _ _
            map_smul' r m := q.pushforwardStructureAlgebraΓRingEquiv.symm.injective <|
              (RingEquiv.symm_apply_apply _ _).trans <| ((g.map_smulₛₗ r m).trans
                (congrArg (_ * ·) (RingEquiv.symm_apply_apply _ _).symm)).trans
                  (q.pushforwardStructureAlgebraΓRingEquiv_symm_smul r
                    (show moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ T.Modules))
                      from q.pushforwardStructureAlgebraΓRingEquiv (g m))).symm }
      left_inv f := by
        ext m
        exact q.pushforwardStructureAlgebraΓRingEquiv.apply_symm_apply
          (show Γ(q.pushforwardStructureAlgebra.X, ⊤) from f m)
      right_inv g := by ext m; exact RingEquiv.symm_apply_apply _ _ }

/-- The linear map of a module map `φ : M~ ⟶ q_* 𝒪_T` sends `m` to the global function on `T`
given by the global section of `φ` at the section of `M~` associated with `m`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv_apply (q : T ⟶ Spec R)
    (M : ModuleCat.{u} R) (φ : tilde M ⟶ (Scheme.Modules.pushforward q).obj (𝟙_ T.Modules))
    (m : M) :
    q.tildeHomPushforwardEquiv M φ m =
      q.pushforwardStructureAlgebraΓRingEquiv.symm (φ.val.app (op ⊤) (tilde.toOpen M ⊤ m)) :=
  (rfl)

/-- The bijection `Scheme.Hom.tildeHomPushforwardEquiv` is natural in the scheme over `Spec R`:
composing a module map with pullback of regular functions along `g : V ⟶ T` composes its linear
map with pullback of global functions along `g`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.tildeHomPushforwardEquiv_comp {V : Scheme.{u}}
    {p : V ⟶ Spec R} {q : T ⟶ Spec R} (g : V ⟶ T) (h : g ≫ q = p) (M : ModuleCat.{u} R)
    (φ : tilde M ⟶ (Scheme.Modules.pushforward q).obj (𝟙_ T.Modules)) (m : M) :
    p.tildeHomPushforwardEquiv M (φ ≫ (Scheme.Hom.pushforwardStructureAlgebraMap g h).hom.hom) m =
      g.appTop (q.tildeHomPushforwardEquiv M φ m) :=
  (congrArg p.pushforwardStructureAlgebraΓRingEquiv.symm
      (CommMon.sectionsAlgHom_apply (Scheme.Hom.pushforwardStructureAlgebraMap g h) ⊤ _).symm).trans
    (Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom g h _)

end

end TauCeti
