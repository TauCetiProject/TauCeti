/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.MulSign
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension.FiberProd
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Extension.Pullback
public import TauCeti.Topology.VectorBundle.SpinStructure.Orientation

/-!
# Twisting a Spin structure by a principal `ℤ/2`-bundle

Let `s` be a Spin structure of rank `n ≥ 1` on a real vector bundle `V` with fibre inner products,
with principal `Spin(n)`-bundle `P`, and let `L` be a principal `ℤ/2`-bundle (a double cover) over
the same base, where `ℤ/2 = Multiplicative (ZMod 2)` is the kernel `{1, -1}` of
`Spin(n) → SO(n)`. The **twist** `s.twist L` (`TauCeti.SpinStructure.twist`) is the Spin structure
with principal bundle

`P ⊗ L = (P ×_X L) ×_μ Spin(n)`,

the extension of structure group of the fibre product `P ×_X L`
(`TauCeti.OrthonormalFrameLift.fiberProd`) along the multiplication by the central signs
`μ : Spin(n) × ℤ/2 → Spin(n)`, `(g, ε) ↦ g ε` (`CliffordAlgebra.realCliffordSpinMulSign`).
Equivalently, `P ⊗ L` is the quotient of `P ×_X L` by `ℤ/2` acting by `(p, l) • ε = (p ε, l ε)`;
in terms of transition functions, it multiplies the transition functions of `P` by the
`±1`-valued transition functions of `L` (this description is not formalized here). Since the
signs act trivially on frames, the frame map of `s` descends: the frame of `[(p, l), a]` is the
frame of `p` composed with the rotation of `a` (`TauCeti.SpinStructure.toFrame_twist_mk`). In
particular the twist induces the same orientation of `V` as `s`
(`TauCeti.SpinStructure.orientation_twist`).

Twisting is functorial in `s` and `L` (`TauCeti.SpinStructure.twistEquiv`), does nothing for the
trivial double cover (`TauCeti.SpinStructure.twistTrivialEquiv`), commutes with pullback
(`TauCeti.SpinStructure.twistPullbackEquiv`), and is an involution: twisting twice by the same
double cover gives back `s` (`TauCeti.SpinStructure.twistTwistEquiv`), by
`[([(p, l), a], l'), b] ↦ p • a ε b`, where `ε` is the sign with `l' = l • ε`. This last fact uses
that every sign squares to one.

This is the action of the double covers of the base on the Spin structures inducing a fixed
orientation of `V`. On paracompact Hausdorff bases the double covers are classified by
`H¹(X; ℤ/2)`, and the action on equivalence classes of Spin structures is free and transitive;
none of these statements is proved here.

## Main definitions

* `TauCeti.SpinStructure.twist`: the twist of a Spin structure by a principal `ℤ/2`-bundle.
* `TauCeti.SpinStructure.twistEquiv`: the equivalence of twists induced by an equivalence of Spin
  structures and an isomorphism of principal `ℤ/2`-bundles.
* `TauCeti.SpinStructure.twistTrivialEquiv`: the twist by the trivial double cover is equivalent to
  the Spin structure.
* `TauCeti.SpinStructure.twistPullbackEquiv`: `(g^* s).twist (g^* L) ≃ g^* (s.twist L)`.
* `TauCeti.SpinStructure.twistTwistEquiv`: twisting twice by the same double cover is equivalent
  to the Spin structure.

## Main results

* `TauCeti.SpinStructure.toFrame_twist_mk`, `TauCeti.SpinStructure.toFrame_twist_inl`: the frame
  map of the twist.
* `TauCeti.SpinStructure.fiberOrientation_twist`, `TauCeti.SpinStructure.orientation_twist`: the
  twist induces the orientation induced by `s`.
* `TauCeti.SpinStructure.twistEquiv_refl`, `TauCeti.SpinStructure.twistEquiv_symm`,
  `TauCeti.SpinStructure.twistEquiv_trans`: twisting respects identities, inverses and
  composites.
* `TauCeti.SpinStructure.twistTwistEquiv_toEquiv_inl`: the formula of the untwisting equivalence.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1, Theorem 1.7.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2020,
  Remark 12.2.28.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinStructure

open OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  (L : X → Type) [TopologicalSpace (TotalSpace (Multiplicative (ZMod 2)) L)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle (Multiplicative (ZMod 2)) L]
  [∀ x, MulAction (Multiplicative (ZMod 2))ᵐᵒᵖ (L x)] [PrincipalBundle (Multiplicative (ZMod 2)) L]

/-- The cyclic group of order two, the kernel `{1, -1}` of `Spin(n) → SO(n)`. -/
local notation "C₂" => Multiplicative (ZMod 2)

/-- The vector action `Spin(n) → SO(n) ⊆ GL(ℝⁿ)` along which Spin structures lift the
orthonormal frame bundle. -/
local notation "ρS" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinToSpecialOrthogonal (realCliffordForm n 0))

/-- The vector action of `Spin(n)` preserves the Euclidean norm of `ℝⁿ`. -/
local notation "hn" => fun g v ↦
  CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n
    (spinToSpecialOrthogonal (realCliffordForm n 0) g) v

/-- The vector action of `Spin(n)` on a fixed vector is continuous in the group element. -/
local notation "hc" => fun v ↦ Continuous.comp
  (CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n v)
  (continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0))

/-- The **twist of a Spin structure by a principal `ℤ/2`-bundle** `L`: the Spin structure with
principal bundle `(P ×_X L) ×_μ Spin(n)`, the extension of structure group of the fibre product of
`P` and `L` along multiplication by the central signs `μ : (g, ε) ↦ g ε`. The frame of
`[(p, l), a]` is the frame of `p` composed with the rotation of `a`
(`TauCeti.SpinStructure.toFrame_twist_mk`). Its body is exposed so that the fibre
`(s.twist L).P x` unfolds to the fibre of the extension downstream. -/
@[expose]
noncomputable def twist (s : SpinStructure F V n) : SpinStructure F V n :=
  (s.fiberProd C₂ L).extend (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc

variable {L} (s : SpinStructure F V n)

/-- The principal bundle of the twist of `s` by `L` is the extension of structure group of the
fibre product of the principal bundle of `s` with `L` along multiplication by the central signs. -/
@[simp]
theorem twist_P :
    (s.twist L).P = Extend (s.fiberProd C₂ L).P (realCliffordSpinMulSign n)
      (continuous_realCliffordSpinMulSign n) :=
  (rfl)

/-- **The frame of `[(p, l), a]`** in the twist of a Spin structure by `L` sends `v` to the frame
of `p` applied to the rotation `a v a⁻¹`. -/
theorem toFrame_twist_mk (x : X) (p : s.P x) (l : L x) (a : realCliffordSpinGroupZero n)
    (v : Fin n → ℝ) :
    TotalSpace.mk' F ((s.twist L).toFrame
        ⟨x, Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l) a⟩).proj
        (((s.twist L).toFrame
          ⟨x, Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
            (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l) a⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (spinVectorAction _ a v))) := by
  refine ((s.fiberProd C₂ L).toFrame_extend_mk (realCliffordSpinMulSign n)
    (continuous_realCliffordSpinMulSign n) _ _ _ x (FiberProd.mk p l) a v).trans ?_
  -- The frame of `(p, l)` in the fibre product is by definition the frame of `p`
  -- (`TauCeti.OrthonormalFrameLift.toFrame_fiberProd_mk`).
  exact congrArg (fun w ↦ TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
    ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 w))) (by simp)

/-- **The frame of `[(p, l), 1]`** in the twist of a Spin structure by `L` is the frame of `p`. -/
@[simp]
theorem toFrame_twist_inl (x : X) (p : s.P x) (l : L x) :
    (s.twist L).toFrame
        ⟨x, Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l)⟩ =
      s.toFrame ⟨x, p⟩ :=
  (s.fiberProd C₂ L).toFrame_extend_inl _ _ _ _ _ x (FiberProd.mk p l)

/-- **Twisting preserves the orientation of the fibres**: the twist of `s` by `L` induces on each
fibre the orientation induced by `s`. -/
@[simp]
theorem fiberOrientation_twist (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    (s.twist L).fiberOrientation o x = s.fiberOrientation o x := by
  obtain ⟨z⟩ := (s.fiberProd C₂ L).nonempty_P x
  have h := (s.twist L).toOrientationCover_toFrame o
    ⟨x, Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
      (P := (s.fiberProd C₂ L).P) (FiberProd.mk (FiberProd.fst (P := s.P) (Q := L) z)
        (FiberProd.snd (P := s.P) (Q := L) z))⟩
  rw [toFrame_twist_inl, s.toOrientationCover_toFrame,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h
  exact h.symm

/-- **Twisting preserves the orientation**: the twist of `s` by `L` induces the orientation of `V`
induced by `s`. -/
@[simp]
theorem orientation_twist (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    (s.twist L).orientation o = s.orientation o := by
  ext x
  rw [orientation_apply, orientation_apply, fiberOrientation_twist]

/-! ### Functoriality -/

variable {L' : X → Type} [TopologicalSpace (TotalSpace C₂ L')] [∀ x, TopologicalSpace (L' x)]
  [FiberBundle C₂ L'] [∀ x, MulAction C₂ᵐᵒᵖ (L' x)] [PrincipalBundle C₂ L']
  {L'' : X → Type} [TopologicalSpace (TotalSpace C₂ L'')] [∀ x, TopologicalSpace (L'' x)]
  [FiberBundle C₂ L''] [∀ x, MulAction C₂ᵐᵒᵖ (L'' x)] [PrincipalBundle C₂ L'']

/-- **Twisting is functorial**: an equivalence `φ : s ≃ t` of Spin structures and an equivalence
`ψ : L ≃ L'` of principal `ℤ/2`-bundles induce an equivalence of twists
`[(p, l), a] ↦ [(φ p, ψ l), a]`. -/
noncomputable def twistEquiv {s t : SpinStructure F V n} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv C₂ L L') : (s.twist L).Equiv (t.twist L') :=
  (φ.fiberProd ψ).extend _ _ _ _ _

@[simp]
theorem twistEquiv_toEquiv_mk {s t : SpinStructure F V n} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv C₂ L L') (x : X) (p : s.P x) (l : L x)
    (a : realCliffordSpinGroupZero n) :
    (twistEquiv φ ψ).toEquiv x
        (Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l) a) =
      Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
        (P := (t.fiberProd C₂ L').P) (FiberProd.mk (φ.toEquiv x p) (ψ.toEquiv x l)) a :=
  (OrthonormalFrameLift.Equiv.extend_toEquiv_mk (realCliffordSpinMulSign n)
    (continuous_realCliffordSpinMulSign n) _ _ _ (φ.fiberProd ψ) x _ a).trans
    (congrArg (fun q ↦ Extend.mk (realCliffordSpinMulSign n)
      (continuous_realCliffordSpinMulSign n) (P := (t.fiberProd C₂ L').P) q a)
      (φ.fiberProd_toEquiv_mk ψ x p l))

@[simp]
theorem twistEquiv_toEquiv_inl {s t : SpinStructure F V n} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv C₂ L L') (x : X) (p : s.P x) (l : L x) :
    (twistEquiv φ ψ).toEquiv x
        (Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l)) =
      Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
        (P := (t.fiberProd C₂ L').P) (FiberProd.mk (φ.toEquiv x p) (ψ.toEquiv x l)) :=
  (OrthonormalFrameLift.Equiv.extend_toEquiv_inl (realCliffordSpinMulSign n)
    (continuous_realCliffordSpinMulSign n) _ _ _ (φ.fiberProd ψ) x _).trans
    (congrArg (Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
      (P := (t.fiberProd C₂ L').P)) (φ.fiberProd_toEquiv_mk ψ x p l))

/-- Twisting by the identity equivalence of `s` and the identity of `L` gives the identity
equivalence of the twist. -/
@[simp]
theorem twistEquiv_refl :
    twistEquiv (OrthonormalFrameLift.Equiv.refl s) (PrincipalBundle.Equiv.refl C₂ L) =
      OrthonormalFrameLift.Equiv.refl (s.twist L) := by
  rw [twistEquiv, OrthonormalFrameLift.Equiv.fiberProd_refl]
  exact OrthonormalFrameLift.Equiv.extend_refl _ _ _ _ _ _

/-- The inverse of the twist by `φ` and `ψ` is the twist by the inverses of `φ` and `ψ`. -/
@[simp]
theorem twistEquiv_symm {s t : SpinStructure F V n} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv C₂ L L') : (twistEquiv φ ψ).symm = twistEquiv φ.symm ψ.symm := by
  rw [twistEquiv, twistEquiv, ← OrthonormalFrameLift.Equiv.fiberProd_symm φ ψ]
  exact (OrthonormalFrameLift.Equiv.extend_symm _ _ _ _ _ _).symm

/-- The composite of the twists by `φ, ψ` and by `φ', ψ'` is the twist by the composites. -/
@[simp]
theorem twistEquiv_trans {s t u : SpinStructure F V n} (φ : s.Equiv t) (φ' : t.Equiv u)
    (ψ : PrincipalBundle.Equiv C₂ L L') (ψ' : PrincipalBundle.Equiv C₂ L' L'') :
    (twistEquiv φ ψ).trans (twistEquiv φ' ψ') = twistEquiv (φ.trans φ') (ψ.trans ψ') := by
  unfold twistEquiv
  rw [← OrthonormalFrameLift.Equiv.fiberProd_trans φ φ' ψ ψ']
  exact (OrthonormalFrameLift.Equiv.extend_trans _ _ _ _ _ _ _).symm

/-! ### The trivial double cover -/

/-- **Twisting by the trivial double cover changes nothing**: the twist of a Spin structure `s` by
the trivial principal `ℤ/2`-bundle is equivalent to `s`, by `[(p, ε), a] ↦ p • ε a`. -/
noncomputable def twistTrivialEquiv : (s.twist (Bundle.Trivial X C₂)).Equiv s :=
  (s.fiberProd C₂ (Bundle.Trivial X C₂)).extendEquivOfEquivariant _ _ _ _ _ s
    (fun _ z ↦ op ((realCliffordSpinDoubleCoverZero n).inl z.snd) • z.fst)
    (fun x z g ↦ by
      obtain ⟨a, ε⟩ := g
      rw [OrthonormalFrameLift.fiberProd_fst_smul, OrthonormalFrameLift.fiberProd_snd_smul,
        unop_op, smul_smul, smul_smul, ← op_mul, ← op_mul, op_smul_eq_mul, map_mul,
        realCliffordSpinMulSign_apply]
      refine congrArg (fun g ↦ op g • _) ?_
      dsimp only
      rw [← mul_assoc, ← mul_assoc,
        Subgroup.mem_center_iff.1 (realCliffordSpinDoubleCoverZero_inl_mem_center n _) a])
    (by
      refine Continuous.totalSpaceMk_smul (G := realCliffordSpinGroupZero n)
        (f := fun z : TotalSpace _ (FiberProd s.P (Bundle.Trivial X C₂)) ↦ z.proj)
        (p := fun z ↦ z.snd.fst) FiberProd.continuous_totalSpaceMk_fst ?_
      exact (continuous_of_discreteTopology (f := ⇑(realCliffordSpinDoubleCoverZero n).inl)).comp
        (continuous_snd.comp ((Bundle.Trivial.homeomorphProd X C₂).continuous.comp
          FiberProd.continuous_totalSpaceMk_snd)))
    (fun x z ↦ s.toFrame_smul_of_map_eq_one (by simp) x z.fst)

@[simp]
theorem twistTrivialEquiv_toEquiv_mk (x : X) (p : s.P x) (ε : C₂)
    (a : realCliffordSpinGroupZero n) :
    s.twistTrivialEquiv.toEquiv x
        (Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ (Bundle.Trivial X C₂)).P)
          (FiberProd.mk (Q := Bundle.Trivial X C₂) p ε) a) =
      op a • op ((realCliffordSpinDoubleCoverZero n).inl ε) • p :=
  OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_mk _ _ _ _ _ _ _ _ _ _ _ x _ a

@[simp]
theorem twistTrivialEquiv_toEquiv_inl (x : X) (p : s.P x) (ε : C₂) :
    s.twistTrivialEquiv.toEquiv x
        (Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ (Bundle.Trivial X C₂)).P)
          (FiberProd.mk (Q := Bundle.Trivial X C₂) p ε)) =
      op ((realCliffordSpinDoubleCoverZero n).inl ε) • p :=
  OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_inl _ _ _ _ _ _ _ _ _ _ _ x _

/-! ### Pullback -/

section Pullback

variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- **The frame of `[(p, l), 1]`** in the pullback of the twist of a Spin structure `s` by `L` is
the frame of `p` in the pullback of `s`. -/
@[simp]
theorem toFrame_pullback_twist_inl (g : K) (y : Y) (p : s.P (g y)) (l : L (g y)) :
    ((s.twist L).pullback g).toFrame
        ⟨y, Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l)⟩ =
      (s.pullback g).toFrame ⟨y, p⟩ :=
  ((s.fiberProd C₂ L).toFrame_pullback_extend_inl _ _ _ _ _ g y (FiberProd.mk p l)).trans
    (s.toFrame_pullback_fiberProd_mk g y p l)

variable [∀ x, Nonempty (L x)]

/-- **Twisting commutes with pullback**: for a continuous map `g : Y → X`,
`(g^* s).twist (g^* L) ≃ g^* (s.twist L)`. Over `y`, both principal bundles are
`(P_{g y} × L_{g y}) ×_μ Spin(n)`, and the equivalence is `[(p, l), a] ↦ [(p, l), a]`. -/
noncomputable def twistPullbackEquiv (g : K) :
    (twist ((g : Y → X) *ᵖ L) (s.pullback g)).Equiv ((s.twist L).pullback g) :=
  ((fiberProdPullbackEquiv (H := C₂) (Q := L) s g).extend (realCliffordSpinMulSign n)
    (continuous_realCliffordSpinMulSign n) _ _ _).trans
      ((s.fiberProd C₂ L).extendPullbackEquiv _ _ _ _ _ g)

/-- The equivalence `(g^* s).twist (g^* L) ≃ g^* (s.twist L)` sends `[(p, l), a]` to
`[(p, l), a]`. -/
theorem twistPullbackEquiv_toEquiv_mk (g : K) (y : Y) (p : s.P (g y)) (l : L (g y))
    (a : realCliffordSpinGroupZero n) :
    (s.twistPullbackEquiv (L := L) g).toEquiv y
        (Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := ((s.pullback g).fiberProd C₂ ((g : Y → X) *ᵖ L)).P) (FiberProd.mk p l) a) =
      Extend.mk (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
        (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l) a := by
  unfold twistPullbackEquiv
  refine (DFunLike.congr_fun (OrthonormalFrameLift.Equiv.trans_toEquiv _ _ y) _).trans ?_
  refine (congrArg (((s.fiberProd C₂ L).extendPullbackEquiv _ _ _ _ _ g).toEquiv y)
    ((Equiv.extend_toEquiv_mk _ _ _ _ _ _ y _ a).trans ?_)).trans
      ((s.fiberProd C₂ L).extendPullbackEquiv_toEquiv_mk _ _ _ _ _ g y _ a)
  exact congrArg (Extend.mk _ _ · a) (fiberProdPullbackEquiv_toEquiv_mk s g y p l)

/-- The equivalence `(g^* s).twist (g^* L) ≃ g^* (s.twist L)` sends `[(p, l), 1]` to
`[(p, l), 1]`. -/
theorem twistPullbackEquiv_toEquiv_inl (g : K) (y : Y) (p : s.P (g y)) (l : L (g y)) :
    (s.twistPullbackEquiv (L := L) g).toEquiv y
        (Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := ((s.pullback g).fiberProd C₂ ((g : Y → X) *ᵖ L)).P) (FiberProd.mk p l)) =
      Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
        (P := (s.fiberProd C₂ L).P) (FiberProd.mk p l) :=
  (congrArg _ (Extend.inl_def _ _ _)).trans
    ((s.twistPullbackEquiv_toEquiv_mk g y p l 1).trans (Extend.inl_def _ _ _).symm)

end Pullback

/-! ### Twisting twice -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The point `p • ε` of `P`, for `((p, l), l')` in `(P ×_X L) ×_X L` and `ε` the sign with
`l' = l • ε`. It is the untwisting map of `TauCeti.SpinStructure.twistTwistEquiv` on
representatives. -/
private noncomputable def untwist (x : X)
    (z : ((s.fiberProd C₂ L).fiberProd C₂ L).P x) : s.P x :=
  op ((realCliffordSpinDoubleCoverZero n).inl (division C₂ z.fst.snd z.snd)) • z.fst.fst

/-- Multiplication by the central signs, applied twice, lifts the double first projection along
the vector action. -/
private theorem comp_comp_prodMap_eq :
    MonoidHom.comp ρS ((realCliffordSpinMulSign n).comp
        ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂))) =
      (MonoidHom.comp ρS (MonoidHom.fst _ C₂)).comp (MonoidHom.fst _ C₂) :=
  MonoidHom.ext fun g ↦
    (DFunLike.congr_fun (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n)
      ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂) g)).trans
    (DFunLike.congr_fun (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) g.1)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
private theorem untwist_smul (x : X) (z : ((s.fiberProd C₂ L).fiberProd C₂ L).P x)
    (g : (realCliffordSpinGroupZero n × C₂) × C₂) :
    untwist s x (op g • z) =
      op ((realCliffordSpinMulSign n).comp ((realCliffordSpinMulSign n).prodMap
        (MonoidHom.id C₂)) g) • untwist s x z := by
  obtain ⟨⟨a, ε⟩, ε'⟩ := g
  -- In `ℤ/2` every element is its own inverse.
  have inv_mul_mul_eq : ∀ ε d ε' : C₂, ε⁻¹ * d * ε' = d * (ε * ε') := by decide
  have key (d : C₂) : a * (realCliffordSpinDoubleCoverZero n).inl (ε⁻¹ * d * ε') =
      (realCliffordSpinDoubleCoverZero n).inl d *
        realCliffordSpinMulSign n (realCliffordSpinMulSign n (a, ε), ε') := by
    rw [inv_mul_mul_eq, realCliffordSpinMulSign_realCliffordSpinMulSign,
      realCliffordSpinMulSign_apply, ← mul_assoc ((realCliffordSpinDoubleCoverZero n).inl d) a,
      ← Subgroup.mem_center_iff.1 (realCliffordSpinDoubleCoverZero_inl_mem_center n d) a,
      mul_assoc a, ← map_mul]
  simp only [untwist, OrthonormalFrameLift.fiberProd_fst_smul,
    OrthonormalFrameLift.fiberProd_snd_smul, unop_op, division_smul_left, division_smul_right,
    smul_smul, ← op_mul]
  exact congrArg (fun g ↦ op g • _) (key _)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
private theorem continuous_untwist :
    Continuous fun z : TotalSpace ((realCliffordSpinGroupZero n × C₂) × C₂)
        ((s.fiberProd C₂ L).fiberProd C₂ L).P ↦
      (⟨z.proj, untwist s z.proj z.snd⟩ : TotalSpace (realCliffordSpinGroupZero n) s.P) := by
  refine Continuous.totalSpaceMk_smul (G := realCliffordSpinGroupZero n)
    (f := fun z : TotalSpace ((realCliffordSpinGroupZero n × C₂) × C₂)
      ((s.fiberProd C₂ L).fiberProd C₂ L).P ↦ z.proj)
    (p := fun z ↦ z.snd.fst.fst)
    (FiberProd.continuous_totalSpaceMk_fst.comp FiberProd.continuous_totalSpaceMk_fst) ?_
  exact (continuous_of_discreteTopology (f := ⇑(realCliffordSpinDoubleCoverZero n).inl)).comp
    (Continuous.division
      (FiberProd.continuous_totalSpaceMk_snd.comp FiberProd.continuous_totalSpaceMk_fst)
      FiberProd.continuous_totalSpaceMk_snd)

/-- **Twisting twice by the same double cover gives back the Spin structure**:
`(s.twist L).twist L ≃ s`, by `[([(p, l), a], l'), b] ↦ p • a ε b`, where `ε` is the sign with
`l' = l • ε` (`TauCeti.SpinStructure.twistTwistEquiv_toEquiv_inl`). It holds because every sign
squares to one. -/
noncomputable def twistTwistEquiv : ((s.twist L).twist L).Equiv s :=
  (((s.fiberProd C₂ L).extendFiberProdEquiv L (realCliffordSpinMulSign n)
      (continuous_realCliffordSpinMulSign n)
      (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc).symm.extend
    (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc).trans <|
  (((s.fiberProd C₂ L).fiberProd C₂ L).extendCompEquiv
    (ρ' := MonoidHom.comp ρS (MonoidHom.fst _ C₂))
    ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂))
    ((continuous_realCliffordSpinMulSign n).prodMap continuous_id)
    (MonoidHom.ext fun g ↦ DFunLike.congr_fun
      (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) g.1)
    (fun k v ↦ CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n
      (spinToSpecialOrthogonal (realCliffordForm n 0) k.1) v)
    (fun v ↦ Continuous.comp (Continuous.comp
      (CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n v)
      (continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0))) continuous_fst)
    (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
    (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc).symm.trans <|
  ((s.fiberProd C₂ L).fiberProd C₂ L).extendEquivOfEquivariant
    ((realCliffordSpinMulSign n).comp ((realCliffordSpinMulSign n).prodMap (MonoidHom.id C₂)))
    ((continuous_realCliffordSpinMulSign n).comp
      ((continuous_realCliffordSpinMulSign n).prodMap continuous_id))
    comp_comp_prodMap_eq hn hc s (untwist s) (untwist_smul s) (continuous_untwist s)
    (fun x _ ↦ s.toFrame_smul_of_map_eq_one (by simp) x _)

/-- The untwisting equivalence `(s.twist L).twist L ≃ s` sends `[([(p, l), 1], l'), 1]` to
`p • ε`, where `ε` is the sign with `l' = l • ε`. -/
@[simp]
theorem twistTwistEquiv_toEquiv_inl (x : X) (p : s.P x) (l l' : L x) :
    (s.twistTwistEquiv (L := L)).toEquiv x
        (Extend.inl (realCliffordSpinMulSign n) (continuous_realCliffordSpinMulSign n)
          (P := ((s.twist L).fiberProd C₂ L).P)
          (FiberProd.mk (Extend.inl (realCliffordSpinMulSign n)
            (continuous_realCliffordSpinMulSign n) (P := (s.fiberProd C₂ L).P)
            (FiberProd.mk p l)) l')) =
      op ((realCliffordSpinDoubleCoverZero n).inl (division C₂ l l')) • p := by
  -- `rw` and `simp` cannot see through the fibres of the iterated twist, so the values of the
  -- three equivalences composed in `twistTwistEquiv` are computed one at a time and chained by
  -- the following two facts about composites and inverses of equivalences of lifts.
  have trans_toEquiv_apply_of_eq {G : Type} [Group G] [TopologicalSpace G]
      {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)} {s t u : OrthonormalFrameLift F V n G ρ}
      (φ : s.Equiv t) (ψ : t.Equiv u) {z : s.P x} {w : t.P x} {r : u.P x}
      (hz : φ.toEquiv x z = w) (hw : ψ.toEquiv x w = r) : (φ.trans ψ).toEquiv x z = r := by
    rw [OrthonormalFrameLift.Equiv.trans_toEquiv, _root_.Equiv.trans_apply, hz, hw]
  have symm_toEquiv_apply_of_eq {G : Type} [Group G] [TopologicalSpace G]
      {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)} {s t : OrthonormalFrameLift F V n G ρ}
      (φ : s.Equiv t) {z : t.P x} {w : s.P x} (h : φ.toEquiv x w = z) :
      φ.symm.toEquiv x z = w := by
    rw [OrthonormalFrameLift.Equiv.symm_toEquiv, _root_.Equiv.symm_apply_eq, h]
  unfold twistTwistEquiv
  apply trans_toEquiv_apply_of_eq
  · exact (OrthonormalFrameLift.Equiv.extend_toEquiv_inl _ _ _ _ _ _ x _).trans
      (congrArg _ (symm_toEquiv_apply_of_eq _
        ((s.fiberProd C₂ L).extendFiberProdEquiv_toEquiv_inl L (realCliffordSpinMulSign n)
          (continuous_realCliffordSpinMulSign n)
          (subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign n) hn hc x
          (FiberProd.mk p l) l')))
  apply trans_toEquiv_apply_of_eq
  · exact symm_toEquiv_apply_of_eq _ (extendCompEquiv_toEquiv_inl ..)
  · exact extendEquivOfEquivariant_toEquiv_inl ..

end SpinStructure

end TauCeti
