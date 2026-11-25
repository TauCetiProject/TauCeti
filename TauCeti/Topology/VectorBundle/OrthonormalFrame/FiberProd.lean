/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Equiv
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

Equivalences of lifts and equivalences of principal `H`-bundles (`TauCeti.PrincipalBundle.Equiv`)
induce equivalences of fibre products (`TauCeti.OrthonormalFrameLift.Equiv.fiberProd`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.fiberProd`: the fibre product of a lift with a principal bundle.
* `TauCeti.OrthonormalFrameLift.Equiv.fiberProd`: the equivalence of fibre products induced by an
  equivalence of lifts and an equivalence of principal bundles.
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

/-- `G × H` acts on the first component of the fibres of the fibre product of a lift with `Q`
through `G`. -/
@[simp]
theorem fiberProd_fst_smul (x : X) (z : (s.fiberProd H Q).P x) (g : (G × H)ᵐᵒᵖ) :
    FiberProd.fst (P := s.P) (Q := Q) (g • z) =
      op g.unop.1 • FiberProd.fst (P := s.P) (Q := Q) z :=
  (rfl)

/-- `G × H` acts on the second component of the fibres of the fibre product of a lift with `Q`
through `H`. -/
@[simp]
theorem fiberProd_snd_smul (x : X) (z : (s.fiberProd H Q).P x) (g : (G × H)ᵐᵒᵖ) :
    FiberProd.snd (P := s.P) (Q := Q) (g • z) =
      op g.unop.2 • FiberProd.snd (P := s.P) (Q := Q) z :=
  (rfl)

variable {Q' : X → Type w} [TopologicalSpace (TotalSpace H Q')] [∀ x, TopologicalSpace (Q' x)]
  [FiberBundle H Q'] [∀ x, MulAction Hᵐᵒᵖ (Q' x)] [PrincipalBundle H Q']
  {Q'' : X → Type w} [TopologicalSpace (TotalSpace H Q'')] [∀ x, TopologicalSpace (Q'' x)]
  [FiberBundle H Q''] [∀ x, MulAction Hᵐᵒᵖ (Q'' x)] [PrincipalBundle H Q'']

/-- **Equivalences of fibre products**: an equivalence `φ : s ≃ t` of lifts along `ρ` and an
equivalence `ψ : Q ≃ Q'` of principal `H`-bundles induce an equivalence of the fibre products
`(p, q) ↦ (φ p, ψ q)`: the equivalence of principal bundles
`TauCeti.PrincipalBundle.Equiv.fiberProd`, which commutes with the frame maps. -/
noncomputable def Equiv.fiberProd {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') : (s.fiberProd H Q).Equiv (t.fiberProd H Q') where
  toPrincipalBundleEquiv := φ.toPrincipalBundleEquiv.fiberProd ψ
  toFrame_map x z := φ.toFrame_map x z.fst

@[simp]
theorem Equiv.fiberProd_toEquiv_mk {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (p : s.P x) (q : Q x) :
    (φ.fiberProd ψ).toEquiv x (FiberProd.mk p q) =
      FiberProd.mk (φ.toEquiv x p) (ψ.toEquiv x q) :=
  (rfl)

@[simp]
theorem Equiv.fiberProd_toEquiv_fst {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (z : (s.fiberProd H Q).P x) :
    FiberProd.fst (P := t.P) (Q := Q') ((φ.fiberProd ψ).toEquiv x z) =
      φ.toEquiv x (FiberProd.fst (P := s.P) (Q := Q) z) :=
  (rfl)

@[simp]
theorem Equiv.fiberProd_toEquiv_snd {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (z : (s.fiberProd H Q).P x) :
    FiberProd.snd (P := t.P) (Q := Q') ((φ.fiberProd ψ).toEquiv x z) =
      ψ.toEquiv x (FiberProd.snd (P := s.P) (Q := Q) z) :=
  (rfl)

@[simp]
theorem Equiv.fiberProd_toEquiv_symm_fst {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (z : (t.fiberProd H Q').P x) :
    FiberProd.fst (P := s.P) (Q := Q) (((φ.fiberProd ψ).toEquiv x).symm z) =
      (φ.toEquiv x).symm (FiberProd.fst (P := t.P) (Q := Q') z) :=
  (rfl)

@[simp]
theorem Equiv.fiberProd_toEquiv_symm_snd {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') (x : X) (z : (t.fiberProd H Q').P x) :
    FiberProd.snd (P := s.P) (Q := Q) (((φ.fiberProd ψ).toEquiv x).symm z) =
      (ψ.toEquiv x).symm (FiberProd.snd (P := t.P) (Q := Q') z) :=
  (rfl)

/-- The identity equivalence of a lift and the identity of `Q` induce the identity equivalence of
the fibre product. -/
@[simp]
theorem Equiv.fiberProd_refl (s : OrthonormalFrameLift F E n G ρ) :
    (refl s).fiberProd (PrincipalBundle.Equiv.refl H Q) = refl (s.fiberProd H Q) := by
  ext x z
  refine FiberProd.ext (P := s.P) (Q := Q) ?_ ?_ <;> simp

/-- The inverse of the equivalence of fibre products induced by `φ` and `ψ` is induced by the
inverses of `φ` and `ψ`. -/
@[simp]
theorem Equiv.fiberProd_symm {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : PrincipalBundle.Equiv H Q Q') : (φ.fiberProd ψ).symm = φ.symm.fiberProd ψ.symm := by
  ext x z
  refine FiberProd.ext (P := s.P) (Q := Q) ?_ ?_ <;> simp

/-- The composite of the equivalences of fibre products induced by `φ, ψ` and by `φ', ψ'` is
induced by the composites `φ.trans φ'` and `ψ.trans ψ'`. -/
@[simp]
theorem Equiv.fiberProd_trans {s t u : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (φ' : t.Equiv u) (ψ : PrincipalBundle.Equiv H Q Q') (ψ' : PrincipalBundle.Equiv H Q' Q'') :
    (φ.fiberProd ψ).trans (φ'.fiberProd ψ') = (φ.trans φ').fiberProd (ψ.trans ψ') := by
  ext x z
  refine FiberProd.ext (P := u.P) (Q := Q'') ?_ ?_ <;> simp

end OrthonormalFrameLift

end TauCeti
