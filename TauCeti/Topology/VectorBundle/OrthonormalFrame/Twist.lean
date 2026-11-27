/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension.Pullback
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.FiberProd

/-!
# Twisting a lift of the orthonormal frame bundle by a principal bundle

Let `s` be a lift of the orthonormal frame bundle of a real vector bundle `E → X` along
`ρ : G →* GL(ℝⁿ)`, with principal `G`-bundle `P`, and let `Q` be a principal `H`-bundle over `X`.
Given a continuous homomorphism `μ : G × H →* G` with `ρ ∘ μ = ρ ∘ fst`, the **twist**
`s.twist Q μ` (`TauCeti.OrthonormalFrameLift.twist`) is the lift along `ρ` with principal bundle

`(P ×_X Q) ×_μ G`,

the extension of structure group (`TauCeti.OrthonormalFrameLift.extend`) of the fibre product
`P ×_X Q` (`TauCeti.OrthonormalFrameLift.fiberProd`) along `μ`. Since `ρ ∘ μ = ρ ∘ fst`, the
frame map descends: the frame of `[(p, q), a]` is the frame of `p` composed with `ρ a`
(`TauCeti.OrthonormalFrameLift.toFrame_twist_mk`).

The typical `μ` is multiplication by a central subgroup of `G` acting trivially on `ℝⁿ`: for a
`Spinᶜ` structure, the central circle (`TauCeti.SpinCStructure.twist`), and for a Spin structure,
the central signs `{±1}` (`TauCeti.SpinStructure.twist`).

Twisting is functorial in the lift and in `Q` (`TauCeti.OrthonormalFrameLift.twistEquiv`). When
`μ (g, 1) = g`, twisting by the trivial bundle changes nothing
(`TauCeti.OrthonormalFrameLift.twistTrivialEquiv`), by `[(p, h), a] ↦ p • μ (1, h) a`. Twisting
commutes with pullback along a continuous map (`TauCeti.OrthonormalFrameLift.twistPullbackEquiv`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.twist`: the twist of a lift by a principal bundle.
* `TauCeti.OrthonormalFrameLift.twistEquiv`: the equivalence of twists induced by an equivalence
  of lifts and an equivalence of principal bundles.
* `TauCeti.OrthonormalFrameLift.twistTrivialEquiv`: the twist by the trivial bundle is equivalent
  to the lift.
* `TauCeti.OrthonormalFrameLift.twistPullbackEquiv`: `(g^* s).twist (g^* Q) ≃ g^* (s.twist Q)`.

## Main results

* `TauCeti.OrthonormalFrameLift.toFrame_twist_mk`, `TauCeti.OrthonormalFrameLift.toFrame_twist_inl`:
  the frame map of the twist.
* `TauCeti.OrthonormalFrameLift.twistEquiv_refl`, `TauCeti.OrthonormalFrameLift.twistEquiv_symm`,
  `TauCeti.OrthonormalFrameLift.twistEquiv_trans`: twisting respects identities, inverses and
  composites.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

open Bundle MulOpposite TauCeti.PrincipalBundle

universe w

namespace TauCeti

namespace OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ}
  {G : Type w} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

section General

variable (s : OrthonormalFrameLift F E n G ρ) {H : Type*} [Group H] [TopologicalSpace H]
  (Q : X → Type w) [TopologicalSpace (TotalSpace H Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle H Q] [∀ x, MulAction Hᵐᵒᵖ (Q x)] [PrincipalBundle H Q]
  (μ : G × H →* G) (hμ : Continuous μ) (hρμ : ρ.comp μ = ρ.comp (MonoidHom.fst G H))
  (hρn : ∀ g v, ‖WithLp.toLp 2 (ρ g v)‖ = ‖WithLp.toLp 2 v‖)
  (hρc : ∀ v, Continuous fun g ↦ ρ g v)

section Construction

variable [ContinuousMul G]

/-- The **twist of a lift by a principal bundle** `Q` along `μ : G × H →* G` with
`ρ ∘ μ = ρ ∘ fst`: the lift along `ρ` with principal bundle `(P ×_X Q) ×_μ G`, the extension of
structure group of the fibre product of `P` and `Q` along `μ`. The frame of `[(p, q), a]` is the
frame of `p` composed with `ρ a` (`TauCeti.OrthonormalFrameLift.toFrame_twist_mk`). Its body is
exposed so that the fibre `(s.twist Q μ …).P x` unfolds to the fibre of the extension
downstream. -/
@[expose]
noncomputable def twist : OrthonormalFrameLift F E n G ρ :=
  (s.fiberProd H Q).extend μ hμ hρμ hρn hρc

variable {Q}

/-- The principal bundle of the twist of `s` by `Q` is the extension of structure group of the
fibre product of the principal bundle of `s` with `Q` along `μ`. -/
@[simp]
theorem twist_P : (s.twist Q μ hμ hρμ hρn hρc).P = Extend (s.fiberProd H Q).P μ hμ :=
  (rfl)

/-- **The frame of `[(p, q), a]`** in the twist of a lift by `Q` sends `v` to the frame of `p`
applied to `ρ a v`. -/
theorem toFrame_twist_mk (x : X) (p : s.P x) (q : Q x) (a : G) (v : Fin n → ℝ) :
    TotalSpace.mk' F ((s.twist Q μ hμ hρμ hρn hρc).toFrame
        ⟨x, Extend.mk μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q) a⟩).proj
        (((s.twist Q μ hμ hρμ hρn hρc).toFrame
          ⟨x, Extend.mk μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q) a⟩).frame
          (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (ρ a v))) :=
  (s.fiberProd H Q).toFrame_extend_mk _ _ _ _ _ x (FiberProd.mk p q) a v

/-- **The frame of `[(p, q), 1]`** in the twist of a lift by `Q` is the frame of `p`. -/
@[simp]
theorem toFrame_twist_inl (x : X) (p : s.P x) (q : Q x) :
    (s.twist Q μ hμ hρμ hρn hρc).toFrame
        ⟨x, Extend.inl μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q)⟩ =
      s.toFrame ⟨x, p⟩ :=
  (s.fiberProd H Q).toFrame_extend_inl _ _ _ _ _ x (FiberProd.mk p q)

end Construction

/-! ### Functoriality -/

section Functoriality

variable [IsTopologicalGroup G] {Q}
  {Q' : X → Type w} [TopologicalSpace (TotalSpace H Q')] [∀ x, TopologicalSpace (Q' x)]
  [FiberBundle H Q'] [∀ x, MulAction Hᵐᵒᵖ (Q' x)] [PrincipalBundle H Q']
  {Q'' : X → Type w} [TopologicalSpace (TotalSpace H Q'')] [∀ x, TopologicalSpace (Q'' x)]
  [FiberBundle H Q''] [∀ x, MulAction Hᵐᵒᵖ (Q'' x)] [PrincipalBundle H Q'']

/-- **Twisting is functorial**: an equivalence `φ : s ≃ t` of lifts and an equivalence
`ψ : Q ≃ Q'` of principal `H`-bundles induce an equivalence of twists
`[(p, q), a] ↦ [(φ p, ψ q), a]`. -/
noncomputable def twistEquiv {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') :
    (s.twist Q μ hμ hρμ hρn hρc).Equiv (t.twist Q' μ hμ hρμ hρn hρc) :=
  (φ.fiberProd ψ).extend μ hμ hρμ hρn hρc

@[simp]
theorem twistEquiv_toEquiv_mk {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (p : s.P x) (q : Q x) (a : G) :
    (twistEquiv μ hμ hρμ hρn hρc φ ψ).toEquiv x
        (Extend.mk μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q) a) =
      Extend.mk μ hμ (P := (t.fiberProd H Q').P)
        (FiberProd.mk (φ.toEquiv x p) (ψ.toEquiv x q)) a :=
  (Equiv.extend_toEquiv_mk μ hμ hρμ hρn hρc (φ.fiberProd ψ) x _ a).trans
    (congrArg (fun z ↦ Extend.mk μ hμ (P := (t.fiberProd H Q').P) z a)
      (φ.fiberProd_toEquiv_mk ψ x p q))

@[simp]
theorem twistEquiv_toEquiv_inl {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (p : s.P x) (q : Q x) :
    (twistEquiv μ hμ hρμ hρn hρc φ ψ).toEquiv x
        (Extend.inl μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q)) =
      Extend.inl μ hμ (P := (t.fiberProd H Q').P)
        (FiberProd.mk (φ.toEquiv x p) (ψ.toEquiv x q)) :=
  (Equiv.extend_toEquiv_inl μ hμ hρμ hρn hρc (φ.fiberProd ψ) x _).trans
    (congrArg (Extend.inl μ hμ (P := (t.fiberProd H Q').P)) (φ.fiberProd_toEquiv_mk ψ x p q))

/-- Twisting by the identity equivalence of `s` and the identity of `Q` gives the identity
equivalence of the twist. -/
@[simp]
theorem twistEquiv_refl :
    twistEquiv μ hμ hρμ hρn hρc (Equiv.refl s) (PrincipalBundle.Equiv.refl H Q) =
      Equiv.refl (s.twist Q μ hμ hρμ hρn hρc) := by
  rw [twistEquiv, Equiv.fiberProd_refl]
  exact Equiv.extend_refl _ _ _ _ _ _

/-- The inverse of the twist by `φ` and `ψ` is the twist by the inverses of `φ` and `ψ`. -/
@[simp]
theorem twistEquiv_symm {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') :
    (twistEquiv μ hμ hρμ hρn hρc φ ψ).symm = twistEquiv μ hμ hρμ hρn hρc φ.symm ψ.symm := by
  rw [twistEquiv, twistEquiv, ← Equiv.fiberProd_symm φ ψ]
  exact (Equiv.extend_symm _ _ _ _ _ _).symm

/-- The composite of the twists by `φ, ψ` and by `φ', ψ'` is the twist by the composites. -/
@[simp]
theorem twistEquiv_trans {s t u : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (φ' : t.Equiv u) (ψ : PrincipalBundle.Equiv H Q Q') (ψ' : PrincipalBundle.Equiv H Q' Q'') :
    (twistEquiv μ hμ hρμ hρn hρc φ ψ).trans (twistEquiv μ hμ hρμ hρn hρc φ' ψ') =
      twistEquiv μ hμ hρμ hρn hρc (φ.trans φ') (ψ.trans ψ') := by
  unfold twistEquiv
  rw [← Equiv.fiberProd_trans φ φ' ψ ψ']
  exact (Equiv.extend_trans _ _ _ _ _ _ _).symm

end Functoriality

end General

/-! ### The trivial bundle -/

section Trivial

variable [IsTopologicalGroup G] (s : OrthonormalFrameLift F E n G ρ)
  {H : Type w} [Group H] [TopologicalSpace H]
  (μ : G × H →* G) (hμ : Continuous μ) (hρμ : ρ.comp μ = ρ.comp (MonoidHom.fst G H))
  (hρn : ∀ g v, ‖WithLp.toLp 2 (ρ g v)‖ = ‖WithLp.toLp 2 v‖)
  (hρc : ∀ v, Continuous fun g ↦ ρ g v)
  (hμ₁ : μ.comp (MonoidHom.inl G H) = MonoidHom.id G)

include hμ₁ in
/-- **Twisting by the trivial bundle changes nothing**: if `μ (g, 1) = g`, the twist of a lift `s`
by the trivial principal `H`-bundle is equivalent to `s`, by `[(p, h), a] ↦ p • μ (1, h) a`. -/
noncomputable def twistTrivialEquiv :
    (s.twist (Bundle.Trivial X H) μ hμ hρμ hρn hρc).Equiv s :=
  (s.fiberProd H (Bundle.Trivial X H)).extendEquivOfEquivariant μ hμ hρμ hρn hρc s
    (fun _ z ↦ op (μ (1, FiberProd.snd (P := s.P) (Q := Bundle.Trivial X H) z)) •
      FiberProd.fst (P := s.P) (Q := Bundle.Trivial X H) z)
    (fun x z g ↦ by
      obtain ⟨a, h⟩ := g
      -- `a μ (1, w h) = μ (1, w) μ (a, h)`, as both are `μ (a, w h)` because `a = μ (a, 1)`.
      have key (w : H) : a * μ (1, w * h) = μ (1, w) * μ (a, h) := by
        have ha : μ (a, 1) = a := DFunLike.congr_fun hμ₁ a
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
        conv_lhs => rw [← ha]
        rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [fiberProd_fst_smul, fiberProd_snd_smul, unop_op, smul_smul, smul_smul, ← op_mul,
        ← op_mul]
      exact congrArg (fun g ↦ op g • _) (key _))
    (by
      refine Continuous.totalSpaceMk_smul (G := G)
        (f := fun z : TotalSpace _ (FiberProd s.P (Bundle.Trivial X H)) ↦ z.proj)
        (p := fun z ↦ z.snd.fst) FiberProd.continuous_totalSpaceMk_fst ?_
      exact (hμ.comp (continuous_const.prodMk continuous_id)).comp
        (continuous_snd.comp ((Bundle.Trivial.homeomorphProd X H).continuous.comp
          FiberProd.continuous_totalSpaceMk_snd)))
    (fun x z ↦ s.toFrame_smul_of_map_eq_one
      ((DFunLike.congr_fun hρμ (1, _)).trans (map_one ρ)) x _)

@[simp]
theorem twistTrivialEquiv_toEquiv_mk (x : X) (p : s.P x) (h : H) (a : G) :
    (s.twistTrivialEquiv μ hμ hρμ hρn hρc hμ₁).toEquiv x
        (Extend.mk μ hμ (P := (s.fiberProd H (Bundle.Trivial X H)).P)
          (FiberProd.mk (Q := Bundle.Trivial X H) p h) a) =
      op a • op (μ (1, h)) • p :=
  extendEquivOfEquivariant_toEquiv_mk _ _ _ _ _ _ _ _ _ _ _ x _ a

@[simp]
theorem twistTrivialEquiv_toEquiv_inl (x : X) (p : s.P x) (h : H) :
    (s.twistTrivialEquiv μ hμ hρμ hρn hρc hμ₁).toEquiv x
        (Extend.inl μ hμ (P := (s.fiberProd H (Bundle.Trivial X H)).P)
          (FiberProd.mk (Q := Bundle.Trivial X H) p h)) =
      op (μ (1, h)) • p :=
  extendEquivOfEquivariant_toEquiv_inl _ _ _ _ _ _ _ _ _ _ _ x _

end Trivial

/-! ### Pullback -/

section Pullback

variable (s : OrthonormalFrameLift F E n G ρ) {H : Type*} [Group H] [TopologicalSpace H]
  {Q : X → Type w} [TopologicalSpace (TotalSpace H Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle H Q] [∀ x, MulAction Hᵐᵒᵖ (Q x)] [PrincipalBundle H Q]
  (μ : G × H →* G) (hμ : Continuous μ) (hρμ : ρ.comp μ = ρ.comp (MonoidHom.fst G H))
  (hρn : ∀ g v, ‖WithLp.toLp 2 (ρ g v)‖ = ‖WithLp.toLp 2 v‖)
  (hρc : ∀ v, Continuous fun g ↦ ρ g v)

variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- **The frame of `[(p, q), 1]`** in the pullback of the twist of a lift `s` by `Q` is the frame
of `p` in the pullback of `s`. -/
@[simp]
theorem toFrame_pullback_twist_inl [ContinuousMul G] (g : K) (y : Y) (p : s.P (g y))
    (q : Q (g y)) :
    ((s.twist Q μ hμ hρμ hρn hρc).pullback g).toFrame
        ⟨y, Extend.inl μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q)⟩ =
      (s.pullback g).toFrame ⟨y, p⟩ :=
  ((s.fiberProd H Q).toFrame_pullback_extend_inl _ _ _ _ _ g y (FiberProd.mk p q)).trans
    (s.toFrame_pullback_fiberProd_mk g y p q)

variable [IsTopologicalGroup G] [∀ x, Nonempty (Q x)]

/-- **Twisting commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).twist (g^* Q) ≃ g^* (s.twist Q)`. Over `y`, both principal bundles are
`(P_{g y} × Q_{g y}) ×_μ G`, and the equivalence is `[(p, q), a] ↦ [(p, q), a]`. Mathlib's
`FiberBundle.pullback` asks for nonempty fibres of `Q` to pull it back. -/
noncomputable def twistPullbackEquiv (g : K) :
    ((s.pullback g).twist ((g : Y → X) *ᵖ Q) μ hμ hρμ hρn hρc).Equiv
      ((s.twist Q μ hμ hρμ hρn hρc).pullback g) :=
  ((fiberProdPullbackEquiv (H := H) (Q := Q) s g).extend μ hμ _ _ _).trans
    ((s.fiberProd H Q).extendPullbackEquiv _ _ _ _ _ g)

/-- The equivalence `(g^* s).twist (g^* Q) ≃ g^* (s.twist Q)` sends `[(p, q), a]` to
`[(p, q), a]`. -/
theorem twistPullbackEquiv_toEquiv_mk (g : K) (y : Y) (p : s.P (g y)) (q : Q (g y)) (a : G) :
    (s.twistPullbackEquiv (Q := Q) μ hμ hρμ hρn hρc g).toEquiv y
        (Extend.mk μ hμ (P := ((s.pullback g).fiberProd H ((g : Y → X) *ᵖ Q)).P)
          (FiberProd.mk p q) a) =
      Extend.mk μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q) a := by
  unfold twistPullbackEquiv
  refine (DFunLike.congr_fun (Equiv.trans_toEquiv _ _ y) _).trans ?_
  refine (congrArg (((s.fiberProd H Q).extendPullbackEquiv _ _ _ _ _ g).toEquiv y)
    ((Equiv.extend_toEquiv_mk _ _ _ _ _ _ y _ a).trans ?_)).trans
      ((s.fiberProd H Q).extendPullbackEquiv_toEquiv_mk _ _ _ _ _ g y _ a)
  exact congrArg (Extend.mk _ _ · a) (fiberProdPullbackEquiv_toEquiv_mk s g y p q)

/-- The equivalence `(g^* s).twist (g^* Q) ≃ g^* (s.twist Q)` sends `[(p, q), 1]` to
`[(p, q), 1]`. -/
theorem twistPullbackEquiv_toEquiv_inl (g : K) (y : Y) (p : s.P (g y)) (q : Q (g y)) :
    (s.twistPullbackEquiv (Q := Q) μ hμ hρμ hρn hρc g).toEquiv y
        (Extend.inl μ hμ (P := ((s.pullback g).fiberProd H ((g : Y → X) *ᵖ Q)).P)
          (FiberProd.mk p q)) =
      Extend.inl μ hμ (P := (s.fiberProd H Q).P) (FiberProd.mk p q) :=
  (congrArg _ (Extend.inl_def _ _ _)).trans
    ((s.twistPullbackEquiv_toEquiv_mk (Q := Q) μ hμ hρμ hρn hρc g y p q 1).trans
      (Extend.inl_def _ _ _).symm)

end Pullback

end OrthonormalFrameLift

end TauCeti
