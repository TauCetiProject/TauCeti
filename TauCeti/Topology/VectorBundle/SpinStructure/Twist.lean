/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.FiberProd
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# Twisting a `Spinᶜ` structure by a principal `U(1)`-bundle

Let `s` be a `Spinᶜ` structure of rank `n ≥ 1` on a real vector bundle `V` with fibre inner
products, with principal `Spinᶜ(n)`-bundle `P`, and let `L` be a principal `U(1)`-bundle over the
same base. The **twist** `s.twist L` (`TauCeti.SpinCStructure.twist`) is the `Spinᶜ` structure
with principal bundle

`P ⊗ L = (P ×_X L) ×_μ Spinᶜ(n)`,

the extension of structure group of the fibre product `P ×_X L`
(`TauCeti.OrthonormalFrameLift.fiberProd`) along the multiplication by the central circle
`μ : Spinᶜ(n) × U(1) → Spinᶜ(n)`, `([s, z], w) ↦ [s, z w]`
(`CliffordAlgebra.spinCGroup.mulCircle`). Since the central circle acts trivially on frames, the
frame map of `s` descends: the frame of `[(p, l), a]` is the frame of `p` composed with the
rotation of `a` (`TauCeti.SpinCStructure.toFrame_twist_mk`). Equivalently, `P ⊗ L` is the quotient
of `P ×_X L` by the circle acting by `(p, l) • w = (p • [1, w], l • w⁻¹)`.

Twisting is functorial: equivalences of `Spinᶜ` structures and equivariant homeomorphisms of
principal `U(1)`-bundles induce equivalences of twists (`TauCeti.SpinCStructure.twistEquiv`), so
the equivalence class of `s.twist L` depends only on the equivalence class of `s` and the
isomorphism class of `L`. Twisting by the trivial bundle changes nothing
(`TauCeti.SpinCStructure.twistTrivialEquiv`): `[(p, w), a] ↦ p • [1, w] a`.

This is the action of the isomorphism classes of complex line bundles on the equivalence classes
of `Spinᶜ` structures. Twisting preserves the orientation induced by `s`; on the classes of
`Spinᶜ` structures inducing a fixed orientation the action is free and transitive. The
isomorphism classes of complex line bundles are identified with Čech `H²(X; ℤ)` for paracompact
Hausdorff bases, and with singular `H²(X; ℤ)` for CW complexes. The determinant line of
`s.twist L` is that of `s` tensored with `L ⊗ L`. None of these statements is proved here.

## Main definitions

* `TauCeti.SpinCStructure.twist`: the twist of a `Spinᶜ` structure by a principal `U(1)`-bundle.
* `TauCeti.SpinCStructure.twistEquiv`: the equivalence of twists induced by an equivalence of
  `Spinᶜ` structures and an isomorphism of principal `U(1)`-bundles.
* `TauCeti.SpinCStructure.twistTrivialEquiv`: the twist by the trivial bundle is equivalent to
  the `Spinᶜ` structure.

## Main results

* `TauCeti.SpinCStructure.toFrame_twist_mk`, `TauCeti.SpinCStructure.toFrame_twist_inl`: the
  frame map of the twist.
* `TauCeti.SpinCStructure.twistEquiv_toEquiv_mk`,
  `TauCeti.SpinCStructure.twistTrivialEquiv_toEquiv_mk`: the formulas of the equivalences of
  twists.
* `TauCeti.SpinCStructure.twistEquiv_refl`, `TauCeti.SpinCStructure.twistEquiv_symm`,
  `TauCeti.SpinCStructure.twistEquiv_trans`: twisting respects identities, inverses and
  composites.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
* D. A. Salamon, *Spin Geometry and Seiberg–Witten Invariants*, 1999, §5.2.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace TauCeti

namespace SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] {n : ℕ} [NeZero n]
  (L : X → Type) [TopologicalSpace (TotalSpace Circle L)] [∀ x, TopologicalSpace (L x)]
  [FiberBundle Circle L] [∀ x, MulAction Circleᵐᵒᵖ (L x)] [PrincipalBundle Circle L]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

/-- The rotation homomorphism `Spinᶜ(n) → GL(ℝⁿ)` along which `Spinᶜ` structures lift the
orthonormal frame bundle. -/
local notation "ρC" => MonoidHom.comp
  (Subgroup.subtype (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)))
  (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQ)

/-- The **twist of a `Spinᶜ` structure by a principal `U(1)`-bundle** `L`: the `Spinᶜ`
structure with principal bundle `(P ×_X L) ×_μ Spinᶜ(n)`, the extension of structure group of
the fibre product of `P` and `L` along multiplication by the central circle
`μ : ([s, z], w) ↦ [s, z w]`. The frame of `[(p, l), a]` is the frame of `p` composed with the
rotation of `a` (`TauCeti.SpinCStructure.toFrame_twist_mk`). -/
noncomputable abbrev twist (s : SpinCStructure F V n) : SpinCStructure F V n :=
  (s.fiberProd Circle L).extend (spinCGroup.mulCircle _ hQ)
    (spinCGroup.continuous_mulCircle _ _)
    (by rw [MonoidHom.comp_assoc, spinCGroup.toSpecialOrthogonal_comp_mulCircle,
      MonoidHom.comp_assoc])
    (fun g ↦ TauCeti.CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n
      (spinCGroup.toSpecialOrthogonal _ _ g))
    (fun v ↦ (TauCeti.CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n
      v).comp (spinCGroup.continuous_toSpecialOrthogonal_pi _ _))

variable {L} (s : SpinCStructure F V n)

/-- **The frame of `[(p, l), a]`** in the twist of a `Spinᶜ` structure by `L` sends `v` to the
frame of `p` applied to the rotation of `a`. -/
theorem toFrame_twist_mk (x : X) (p : s.P x) (l : L x)
    (a : spinCGroup (realCliffordForm n 0) hQ) (v : Fin n → ℝ) :
    TotalSpace.mk' F ((s.twist L).toFrame
        ⟨x, Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) a⟩).proj
        (((s.twist L).toFrame
          ⟨x, Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
            (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) a⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (s.toFrame ⟨x, p⟩).proj
        ((s.toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (ρC a v))) :=
  (s.fiberProd Circle L).toFrame_extend_mk _ _ _ _ _ x (FiberProd.mk p l) a v

/-- **The frame of `[(p, l), 1]`** in the twist of a `Spinᶜ` structure by `L` is the frame of
`p`. -/
@[simp]
theorem toFrame_twist_inl (x : X) (p : s.P x) (l : L x) :
    (s.twist L).toFrame
        ⟨x, Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk p l)⟩ =
      s.toFrame ⟨x, p⟩ :=
  (s.fiberProd Circle L).toFrame_extend_inl _ _ _ _ _ x (FiberProd.mk p l)

/-- **Twisting is functorial**: an equivalence `φ : s ≃ t` of `Spinᶜ` structures and a fibrewise
equivariant bijection `ψ` from `L` to a principal `U(1)`-bundle `L'`, continuous on total spaces
in both directions, induce an equivalence of twists `[(p, l), a] ↦ [(φ p, ψ l), a]`. -/
noncomputable def twistEquiv {s t : SpinCStructure F V n} (φ : s.Equiv t)
    {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
    [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']
    (ψ : ∀ x, L x ≃ L' x) (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (hψc' : Continuous fun l : TotalSpace Circle L' ↦
      (⟨l.proj, (ψ l.proj).symm l.snd⟩ : TotalSpace Circle L)) :
    (s.twist L).Equiv (t.twist L') :=
  (φ.fiberProd ψ hψ hψc hψc').extend _ _ _ _ _

@[simp]
theorem twistEquiv_toEquiv_mk {s t : SpinCStructure F V n} (φ : s.Equiv t)
    {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
    [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']
    (ψ : ∀ x, L x ≃ L' x) (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (hψc' : Continuous fun l : TotalSpace Circle L' ↦
      (⟨l.proj, (ψ l.proj).symm l.snd⟩ : TotalSpace Circle L))
    (x : X) (p : s.P x) (l : L x) (a : spinCGroup (realCliffordForm n 0) hQ) :
    (twistEquiv φ ψ hψ hψc hψc').toEquiv x
        (Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk p l) a) =
      Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
        (P := (t.fiberProd Circle L').P) (FiberProd.mk (φ.toEquiv x p) (ψ x l)) a :=
  (OrthonormalFrameLift.Equiv.extend_toEquiv_mk _ _ _ _ _ _ x _ a).trans
    (congrArg (fun q ↦ Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
      (P := (t.fiberProd Circle L').P) q a) (φ.fiberProd_toEquiv_mk ψ hψ hψc hψc' x p l))

@[simp]
theorem twistEquiv_toEquiv_inl {s t : SpinCStructure F V n} (φ : s.Equiv t)
    {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
    [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']
    (ψ : ∀ x, L x ≃ L' x) (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (hψc' : Continuous fun l : TotalSpace Circle L' ↦
      (⟨l.proj, (ψ l.proj).symm l.snd⟩ : TotalSpace Circle L))
    (x : X) (p : s.P x) (l : L x) :
    (twistEquiv φ ψ hψ hψc hψc').toEquiv x
        (Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle L).P) (FiberProd.mk p l)) =
      Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
        (P := (t.fiberProd Circle L').P) (FiberProd.mk (φ.toEquiv x p) (ψ x l)) :=
  (OrthonormalFrameLift.Equiv.extend_toEquiv_inl _ _ _ _ _ _ x _).trans
    (congrArg (Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
      (P := (t.fiberProd Circle L').P)) (φ.fiberProd_toEquiv_mk ψ hψ hψc hψc' x p l))

/-- Twisting by the identity equivalence of `s` and the identity of `L` gives the identity
equivalence of the twist. -/
@[simp]
theorem twistEquiv_refl
    (hψ : ∀ x (l : L x) (w : Circle), _root_.Equiv.refl (L x) (op w • l) =
      op w • _root_.Equiv.refl (L x) l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, _root_.Equiv.refl (L l.proj) l.snd⟩ : TotalSpace Circle L))
    (hψc' : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, (_root_.Equiv.refl (L l.proj)).symm l.snd⟩ : TotalSpace Circle L)) :
    twistEquiv (OrthonormalFrameLift.Equiv.refl s) (fun x ↦ _root_.Equiv.refl (L x)) hψ hψc hψc' =
      OrthonormalFrameLift.Equiv.refl (s.twist L) := by
  rw [twistEquiv, OrthonormalFrameLift.Equiv.fiberProd_refl]
  exact OrthonormalFrameLift.Equiv.extend_refl _ _ _ _ _ _

/-- The inverse of the twist by `φ` and `ψ` is the twist by the inverses of `φ` and `ψ`. -/
@[simp]
theorem twistEquiv_symm {s t : SpinCStructure F V n} (φ : s.Equiv t)
    {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
    [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']
    (ψ : ∀ x, L x ≃ L' x) (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (hψc' : Continuous fun l : TotalSpace Circle L' ↦
      (⟨l.proj, (ψ l.proj).symm l.snd⟩ : TotalSpace Circle L)) :
    (twistEquiv φ ψ hψ hψc hψc').symm =
      twistEquiv φ.symm (fun x ↦ (ψ x).symm)
        (fun x l w ↦ (ψ x).symm_apply_eq.2 (by rw [hψ, _root_.Equiv.apply_symm_apply]))
        hψc' hψc := by
  rw [twistEquiv, twistEquiv, ← OrthonormalFrameLift.Equiv.fiberProd_symm φ ψ hψ hψc hψc']
  exact (OrthonormalFrameLift.Equiv.extend_symm _ _ _ _ _ _).symm

/-- The composite of the twists by `φ, ψ` and by `φ', ψ'` is the twist by the composites. -/
@[simp]
theorem twistEquiv_trans {s t u : SpinCStructure F V n} (φ : s.Equiv t) (φ' : t.Equiv u)
    {L' : X → Type} [TopologicalSpace (TotalSpace Circle L')] [∀ x, TopologicalSpace (L' x)]
    [FiberBundle Circle L'] [∀ x, MulAction Circleᵐᵒᵖ (L' x)] [PrincipalBundle Circle L']
    {L'' : X → Type} [TopologicalSpace (TotalSpace Circle L'')] [∀ x, TopologicalSpace (L'' x)]
    [FiberBundle Circle L''] [∀ x, MulAction Circleᵐᵒᵖ (L'' x)] [PrincipalBundle Circle L'']
    (ψ : ∀ x, L x ≃ L' x) (hψ : ∀ x (l : L x) (w : Circle), ψ x (op w • l) = op w • ψ x l)
    (hψc : Continuous fun l : TotalSpace Circle L ↦
      (⟨l.proj, ψ l.proj l.snd⟩ : TotalSpace Circle L'))
    (hψc' : Continuous fun l : TotalSpace Circle L' ↦
      (⟨l.proj, (ψ l.proj).symm l.snd⟩ : TotalSpace Circle L))
    (ψ' : ∀ x, L' x ≃ L'' x) (hψ' : ∀ x (l : L' x) (w : Circle), ψ' x (op w • l) = op w • ψ' x l)
    (hψ'c : Continuous fun l : TotalSpace Circle L' ↦
      (⟨l.proj, ψ' l.proj l.snd⟩ : TotalSpace Circle L''))
    (hψ'c' : Continuous fun l : TotalSpace Circle L'' ↦
      (⟨l.proj, (ψ' l.proj).symm l.snd⟩ : TotalSpace Circle L')) :
    (twistEquiv φ ψ hψ hψc hψc').trans (twistEquiv φ' ψ' hψ' hψ'c hψ'c') =
      twistEquiv (φ.trans φ') (fun x ↦ (ψ x).trans (ψ' x))
        (fun x l w ↦ by simp only [_root_.Equiv.trans_apply, hψ, hψ'])
        (hψ'c.comp hψc) (hψc'.comp hψ'c') := by
  unfold twistEquiv
  rw [← OrthonormalFrameLift.Equiv.fiberProd_trans φ φ' ψ hψ hψc hψc' ψ' hψ' hψ'c hψ'c']
  exact (OrthonormalFrameLift.Equiv.extend_trans _ _ _ _ _ _ _).symm

/-- **Twisting by the trivial bundle changes nothing**: the twist of a `Spinᶜ` structure `s` by
the trivial principal `U(1)`-bundle is equivalent to `s`, by `[(p, w), a] ↦ p • [1, w] a`. -/
noncomputable def twistTrivialEquiv : (s.twist (Bundle.Trivial X Circle)).Equiv s :=
  (s.fiberProd Circle (Bundle.Trivial X Circle)).extendEquivOfEquivariant _ _ _ _ _ s
    (fun x z ↦ op (spinCGroup.ofCircle _ hQ z.snd) • z.fst)
    (fun x z g ↦ by
      obtain ⟨a, w⟩ := g
      rw [OrthonormalFrameLift.fiberProd_fst_smul, OrthonormalFrameLift.fiberProd_snd_smul,
        unop_op, smul_smul, smul_smul, ← op_mul, ← op_mul, op_smul_eq_mul,
        spinCGroup.ofCircle_mul_mulCircle, spinCGroup.mulCircle_apply])
    (by
      refine Continuous.totalSpaceMk_smul (G := spinCGroup (realCliffordForm n 0) hQ)
        (f := fun z : TotalSpace _ (FiberProd s.P (Bundle.Trivial X Circle)) ↦ z.proj)
        (p := fun z ↦ z.snd.fst) FiberProd.continuous_totalSpaceMk_fst ?_
      exact (spinCGroup.continuous_ofCircle _ _).comp
        (continuous_snd.comp ((Bundle.Trivial.homeomorphProd X Circle).continuous.comp
          FiberProd.continuous_totalSpaceMk_snd)))
    (fun x z ↦ s.toFrame_smul_ofCircle x z.fst z.snd)

@[simp]
theorem twistTrivialEquiv_toEquiv_mk (x : X) (p : s.P x) (w : Circle)
    (a : spinCGroup (realCliffordForm n 0) hQ) :
    s.twistTrivialEquiv.toEquiv x
        (Extend.mk (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle (Bundle.Trivial X Circle)).P)
          (FiberProd.mk (Q := Bundle.Trivial X Circle) p w) a) =
      op a • op (spinCGroup.ofCircle _ hQ w) • p :=
  OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_mk _ _ _ _ _ _ _ _ _ _ _ x _ a

@[simp]
theorem twistTrivialEquiv_toEquiv_inl (x : X) (p : s.P x) (w : Circle) :
    s.twistTrivialEquiv.toEquiv x
        (Extend.inl (spinCGroup.mulCircle _ hQ) (spinCGroup.continuous_mulCircle _ _)
          (P := (s.fiberProd Circle (Bundle.Trivial X Circle)).P)
          (FiberProd.mk (Q := Bundle.Trivial X Circle) p w)) =
      op (spinCGroup.ofCircle _ hQ w) • p :=
  OrthonormalFrameLift.extendEquivOfEquivariant_toEquiv_inl _ _ _ _ _ _ _ _ _ _ _ x _

end SpinCStructure

end TauCeti
