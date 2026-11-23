/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.FiberProd
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic
public import Mathlib.GroupTheory.NoncommCoprod

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

This is the action of the isomorphism classes of complex line bundles, equivalently of
`H²(X; ℤ)` on paracompact bases, on the equivalence classes of `Spinᶜ` structures; on such bases
it is free and transitive whenever a `Spinᶜ` structure exists, and the determinant line of
`s.twist L` is that of `s` tensored with `L ⊗ L`. Neither statement is proved here.

## Main definitions

* `CliffordAlgebra.spinCGroup.mulCircle`: the multiplication `Spinᶜ(Q) × U(1) → Spinᶜ(Q)`,
  `(a, w) ↦ a [1, w]`, a homomorphism because the circle is central.
* `TauCeti.SpinCStructure.twist`: the twist of a `Spinᶜ` structure by a principal `U(1)`-bundle.
* `TauCeti.SpinCStructure.twistEquiv`: the equivalence of twists induced by an equivalence of
  `Spinᶜ` structures and an isomorphism of principal `U(1)`-bundles.
* `TauCeti.SpinCStructure.twistTrivialEquiv`: the twist by the trivial bundle is equivalent to
  the `Spinᶜ` structure.

## Main results

* `TauCeti.SpinCStructure.toFrame_twist_mk`, `TauCeti.SpinCStructure.toFrame_twist_inl`: the
  frame map of the twist.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
* D. A. Salamon, *Spin Geometry and Seiberg–Witten Invariants*, 1999, §5.2.
-/

public section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle

namespace CliffordAlgebra.spinCGroup

variable {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ M) (hQ : Q ≠ 0)

/-- **Multiplication by the central circle**, `Spinᶜ(Q) × U(1) → Spinᶜ(Q)`, `(a, w) ↦ a [1, w]`;
on classes, `([s, z], w) ↦ [s, z w]`. It is a homomorphism because the circle `[1, w]` is
central (`CliffordAlgebra.spinCGroup.ofCircle_mem_center`). -/
noncomputable def mulCircle : spinCGroup Q hQ × Circle →* spinCGroup Q hQ :=
  (MonoidHom.id _).noncommCoprod (ofCircle Q hQ) fun a w ↦
    Subgroup.mem_center_iff.1 (ofCircle_mem_center Q hQ w) a

@[simp]
theorem mulCircle_apply (a : spinCGroup Q hQ) (w : Circle) :
    mulCircle Q hQ (a, w) = a * ofCircle Q hQ w :=
  (rfl)

/-- Multiplication by the central circle sends `([s, z], w)` to `[s, z w]`. -/
theorem mulCircle_mk (s : spinGroup Q) (z w : Circle) :
    mulCircle Q hQ (mk Q hQ (s, z), w) = mk Q hQ (s, z * w) := by
  rw [mulCircle_apply, ofCircle_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

/-- Multiplication by the central circle does not change the rotation. -/
@[simp]
theorem toSpecialOrthogonal_mulCircle (g : spinCGroup Q hQ × Circle) :
    toSpecialOrthogonal Q hQ (mulCircle Q hQ g) = toSpecialOrthogonal Q hQ g.1 := by
  obtain ⟨a, w⟩ := g
  rw [mulCircle_apply, map_mul, toSpecialOrthogonal_ofCircle, mul_one]

/-- Multiplication by the central circle is continuous. -/
@[fun_prop]
theorem continuous_mulCircle [ContinuousMul (spinCGroup Q hQ)] : Continuous (mulCircle Q hQ) := by
  have h : Continuous fun g : spinCGroup Q hQ × Circle ↦ g.1 * ofCircle Q hQ g.2 :=
    continuous_fst.mul ((continuous_ofCircle Q hQ).comp continuous_snd)
  exact h.congr fun g ↦ (mulCircle_apply Q hQ g.1 g.2).symm

end CliffordAlgebra.spinCGroup

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

/-- Multiplication by the central circle lifts the first projection along the rotation
homomorphism. -/
theorem rotation_comp_mulCircle :
    MonoidHom.comp ρC (spinCGroup.mulCircle (realCliffordForm n 0) hQ) =
      MonoidHom.comp ρC (MonoidHom.fst _ Circle) :=
  MonoidHom.ext fun g ↦ by simp

/-- The **twist of a `Spinᶜ` structure by a principal `U(1)`-bundle** `L`: the `Spinᶜ`
structure with principal bundle `(P ×_X L) ×_μ Spinᶜ(n)`, the extension of structure group of
the fibre product of `P` and `L` along multiplication by the central circle
`μ : ([s, z], w) ↦ [s, z w]`. The frame of `[(p, l), a]` is the frame of `p` composed with the
rotation of `a` (`TauCeti.SpinCStructure.toFrame_twist_mk`). -/
noncomputable abbrev twist (s : SpinCStructure F V n) : SpinCStructure F V n :=
  (s.fiberProd Circle L).extend (spinCGroup.mulCircle _ hQ)
    (spinCGroup.continuous_mulCircle _ _) rotation_comp_mulCircle
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

/-- **Twisting by the trivial bundle changes nothing**: the twist of a `Spinᶜ` structure `s` by
the trivial principal `U(1)`-bundle is equivalent to `s`, by `[(p, w), a] ↦ p • [1, w] a`. -/
noncomputable def twistTrivialEquiv : (s.twist (Bundle.Trivial X Circle)).Equiv s :=
  (s.fiberProd Circle (Bundle.Trivial X Circle)).extendEquivOfEquivariant _ _ _ _ _ s
    (fun x z ↦ op (spinCGroup.ofCircle _ hQ z.snd) • z.fst)
    (fun x z g ↦ by
      obtain ⟨a, w⟩ := g
      revert z
      change ∀ z : FiberProd s.P (Bundle.Trivial X Circle) x,
        op (spinCGroup.ofCircle _ hQ (op (a, w) • z).snd) • (op (a, w) • z).fst =
          op (spinCGroup.mulCircle _ hQ (a, w)) • op (spinCGroup.ofCircle _ hQ z.snd) • z.fst
      intro z
      rw [FiberProd.fst_smul, FiberProd.snd_smul, unop_op, ← mul_smul, ← mul_smul, ← op_mul,
        ← op_mul, spinCGroup.mulCircle_apply]
      congr 2
      change a * spinCGroup.ofCircle _ hQ (z.snd * w) = _
      rw [map_mul, ← mul_assoc,
        Subgroup.mem_center_iff.1 (spinCGroup.ofCircle_mem_center _ hQ z.snd) a, mul_assoc])
    (by
      refine Continuous.totalSpaceMk_smul (G := spinCGroup (realCliffordForm n 0) hQ)
        (f := fun z : TotalSpace _ (FiberProd s.P (Bundle.Trivial X Circle)) ↦ z.proj)
        (p := fun z ↦ z.snd.fst) FiberProd.continuous_totalSpaceMk_fst ?_
      exact (spinCGroup.continuous_ofCircle _ _).comp
        (continuous_snd.comp ((Bundle.Trivial.homeomorphProd X Circle).continuous.comp
          FiberProd.continuous_totalSpaceMk_snd)))
    (fun x z ↦ s.toFrame_smul_ofCircle x z.fst z.snd)

end SpinCStructure

end TauCeti
