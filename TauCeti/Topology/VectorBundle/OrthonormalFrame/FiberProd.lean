/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Prod
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift.Basic

/-!
# The fibre product of a lift of the orthonormal frame bundle with a principal bundle

Let `s` be a lift of the orthonormal frame bundle of a real vector bundle `E` along
`ρ : G →* GL(ℝⁿ)`, with principal `G`-bundle `P`, and let `Q` be a principal `H`-bundle over the
same base. The **fibre product** `s.fiberProd H Q` is the lift along `ρ ∘ fst : G × H →* GL(ℝⁿ)`
whose principal bundle is the fibre product `P ×_X Q`
(`TauCeti.PrincipalBundle.FiberProd`) and whose frame map forgets the point of `Q`: the frame of
`(p, q)` is the frame of `p` (`TauCeti.OrthonormalFrameLift.toFrame_fiberProd_mk`).

Extending the fibre product along a homomorphism `G × H →* K` combines the lift with `Q`. For a
`Spinᶜ` structure and a principal `U(1)`-bundle `L`, extending along the multiplication
`Spinᶜ(n) × U(1) → Spinᶜ(n)`, `([s, z], w) ↦ [s, z w]`, twists the `Spinᶜ` structure by `L`
(`TauCeti.SpinCStructure.twist`).

Equivalences of lifts and fibrewise equivariant homeomorphisms of principal `H`-bundles induce
equivalences of fibre products (`TauCeti.OrthonormalFrameLift.Equiv.fiberProd`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.fiberProd`: the fibre product of a lift with a principal bundle.
* `TauCeti.OrthonormalFrameLift.Equiv.fiberProd`: the equivalence of fibre products induced by an
  equivalence of lifts and an equivariant homeomorphism of principal bundles.
-/

public section

open Bundle MulOpposite TauCeti.PrincipalBundle

universe w

namespace TauCeti

namespace OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}
  (H : Type*) [Group H] [TopologicalSpace H]
  (Q : X → Type w) [TopologicalSpace (TotalSpace H Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle H Q] [∀ x, MulAction Hᵐᵒᵖ (Q x)] [PrincipalBundle H Q]

/-- The **fibre product of a lift with a principal bundle**: for a lift `s` along `ρ` with
principal `G`-bundle `P` and a principal `H`-bundle `Q` over the same base, the lift along
`ρ ∘ fst` whose principal `(G × H)`-bundle is the fibre product `P ×_X Q`, the frame of `(p, q)`
being the frame of `p`. Its body is exposed so that the fibre `(s.fiberProd H Q).P x` unfolds to
`FiberProd s.P Q x` downstream. -/
@[expose]
noncomputable def fiberProd (s : OrthonormalFrameLift F E n G ρ) :
    OrthonormalFrameLift F E n (G × H) (ρ.comp (MonoidHom.fst G H)) where
  P := FiberProd s.P Q
  toFrame z := s.toFrame ⟨z.proj, z.snd.fst⟩
  continuous_toFrame := s.continuous_toFrame.comp FiberProd.continuous_totalSpaceMk_fst
  proj_toFrame z := s.proj_toFrame _
  toFrame_smul x z g v := by
    rw [FiberProd.fst_smul (P := s.P) (Q := Q) z (op g), unop_op]
    exact s.toFrame_smul x z.fst g.1 v

variable (s : OrthonormalFrameLift F E n G ρ)

/-- The principal bundle of the fibre product of a lift with `Q` is the fibre product of the
principal bundle of the lift with `Q`. -/
@[simp]
theorem fiberProd_P : (s.fiberProd H Q).P = FiberProd s.P Q :=
  (rfl)

/-- **The frame of `(p, q)`** in the fibre product of a lift with a principal bundle is the frame
of `p`. -/
@[simp]
theorem toFrame_fiberProd_mk (x : X) (p : s.P x) (q : Q x) :
    (s.fiberProd H Q).toFrame ⟨x, FiberProd.mk p q⟩ = s.toFrame ⟨x, p⟩ :=
  (rfl)

variable {H Q}

/-- **Equivalences of fibre products**: an equivalence `φ : s ≃ t` of lifts along `ρ` and a
fibrewise equivariant bijection `ψ` from `Q` to a principal `H`-bundle `Q'`, continuous on total
spaces in both directions, induce an equivalence of the fibre products
`(p, q) ↦ (φ p, ψ q)`. -/
noncomputable def Equiv.fiberProd {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    {Q' : X → Type w} [TopologicalSpace (TotalSpace H Q')] [∀ x, TopologicalSpace (Q' x)]
    [FiberBundle H Q'] [∀ x, MulAction Hᵐᵒᵖ (Q' x)] [PrincipalBundle H Q']
    (ψ : ∀ x, Q x ≃ Q' x) (hψ : ∀ x (q : Q x) (h : H), ψ x (op h • q) = op h • ψ x q)
    (hψc : Continuous fun q : TotalSpace H Q ↦ (⟨q.proj, ψ q.proj q.snd⟩ : TotalSpace H Q'))
    (hψc' : Continuous fun q : TotalSpace H Q' ↦
      (⟨q.proj, (ψ q.proj).symm q.snd⟩ : TotalSpace H Q)) :
    (s.fiberProd H Q).Equiv (t.fiberProd H Q') where
  toEquiv x :=
    { toFun z := FiberProd.mk (φ.toEquiv x z.fst) (ψ x z.snd)
      invFun z := FiberProd.mk ((φ.toEquiv x).symm z.fst) ((ψ x).symm z.snd)
      left_inv z := by simp [FiberProd.mk_fst_snd (P := s.P) (Q := Q) z]
      right_inv z := by simp [FiberProd.mk_fst_snd (P := t.P) (Q := Q') z] }
  continuous_toFun :=
    (φ.continuous_toFun.comp FiberProd.continuous_totalSpaceMk_fst).totalSpaceMk_fiberProdMk
      (hψc.comp FiberProd.continuous_totalSpaceMk_snd)
  continuous_invFun :=
    (φ.continuous_invFun.comp FiberProd.continuous_totalSpaceMk_fst).totalSpaceMk_fiberProdMk
      (hψc'.comp FiberProd.continuous_totalSpaceMk_snd)
  map_smul x z g := congrArg₂ FiberProd.mk (φ.map_smul x z.fst g.1) (hψ x z.snd g.2)
  toFrame_map x z := φ.toFrame_map x z.fst

@[simp]
theorem Equiv.fiberProd_toEquiv_mk {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    {Q' : X → Type w} [TopologicalSpace (TotalSpace H Q')] [∀ x, TopologicalSpace (Q' x)]
    [FiberBundle H Q'] [∀ x, MulAction Hᵐᵒᵖ (Q' x)] [PrincipalBundle H Q']
    (ψ : ∀ x, Q x ≃ Q' x) (hψ : ∀ x (q : Q x) (h : H), ψ x (op h • q) = op h • ψ x q)
    (hψc : Continuous fun q : TotalSpace H Q ↦ (⟨q.proj, ψ q.proj q.snd⟩ : TotalSpace H Q'))
    (hψc' : Continuous fun q : TotalSpace H Q' ↦
      (⟨q.proj, (ψ q.proj).symm q.snd⟩ : TotalSpace H Q))
    (x : X) (p : s.P x) (q : Q x) :
    (φ.fiberProd ψ hψ hψc hψc').toEquiv x (FiberProd.mk p q) =
      FiberProd.mk (φ.toEquiv x p) (ψ x q) :=
  (rfl)

end OrthonormalFrameLift

end TauCeti
