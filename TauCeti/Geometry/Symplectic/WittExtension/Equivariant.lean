/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel.Equivariant
public import TauCeti.Geometry.Symplectic.LinearReduction
public import TauCeti.Geometry.Symplectic.Prod.Basic
import TauCeti.RepresentationTheory.Semisimple

/-!
# The equivariant presymplectic Witt extension

Let a group `G` act linearly on a finite-dimensional real symplectic vector space `(E, ω)` by a
semisimple representation `ρ` preserving `ω`, and let `ι : W → E` be an injective `G`-equivariant
linear map from a representation `σ` of `G` on `W`, pulling `ω` back to an alternating form `B`.
Put `K = ker B`, so that `ι` carries `K` onto the radical `ι W ∩ (ι W)^ω`, and let
`V = (ι W)^ω ⧸ (ι W ∩ (ι W)^ω)` be the reduced space of `(ι W)^ω`, the *symplectic normal space*,
with its reduced symplectic form `ω_V` and an action `πV` of `G` induced by `ρ`. For a projection
`P : W → K` which is `G`-equivariant, the group acts on the coisotropic model `W × K*`
(`LinearMap.BilinForm.IsAlt.coisotropicModel`) through `σ` on `W` and the dual of its restriction to
`K` on `K*`, preserving the model form
(`LinearMap.BilinForm.IsAlt.isInvariantForm_coisotropicModel`).

The main theorem is the **equivariant presymplectic Witt extension**,
`LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel_prod_reduction`:
`ι` extends to a `G`-equivariant linear symplectomorphism

`(W × K*) × V ≃ E`, `((w, 0), 0) ↦ ι w`,

from the direct sum of the coisotropic model and `(V, ω_V)`, which maps each `((0, 0), v)` into
`(ι W)^ω` with class `v` in `V`. This is the linear part of the Marle–Guillemin–Sternberg local
normal form of a Hamiltonian action near an orbit: there `W` is the orbit tangent space, `G` the
stabilizer and `V` the symplectic slice. For a coisotropic image `V` is zero, and the statement
recovers `LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel`.

The proof reduces to that coisotropic case. An equivariant section `s` of `(ι W)^ω → V`
(`TauCeti.SymplecticForm.exists_equivariant_lift_reducedSpace`) makes `(w, v) ↦ ι w + s v` an
equivariant embedding of `W × V` into `E` with coisotropic image `ι W + s V`, and
`(w, v) ↦ ((w, 0), v)` is one into the model. Both pull back `B ⊕ ω_V`, so the equivariant Witt
extension from coisotropic subspaces
(`TauCeti.SymplecticForm.exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic`) joins
them.

Semisimplicity cannot be dropped: the shear `(q, p) ↦ (q + p, p)` of `ℝ²` generates a symplectic
action of `ℤ` fixing the Lagrangian line `W = ℝ × 0`, on which `B = 0`, `K = W` and `V = 0`; the
model `W × W*` then carries the trivial action, which is not conjugate to the shear.

## Main results

* `LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel_prod_reduction`
  is the equivariant presymplectic Witt extension.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Reidel, 1984, 161–175.
* J.-P. Ortega and T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Birkhäuser, 2004,
  Sections 7.1–7.2 (the symplectic slice and the linear model).
-/

public section

open Module TauCeti TauCeti.Representation TauCeti.SymplecticForm

namespace LinearMap.BilinForm.IsAlt

variable {G W E : Type*} [Group G] [AddCommGroup W] [Module ℝ W] [AddCommGroup E] [Module ℝ E]
  {B : LinearMap.BilinForm ℝ W} {σ : Representation ℝ G W} {ρ : Representation ℝ G E}
  {ω : SymplecticForm E} {ι : W →ₗ[ℝ] E}

/-- The action of `G` on the model `(W × K*) × V` preserves the sum of the coisotropic model form
and the reduced form. -/
private theorem isInvariantForm_model (hB : B.IsAlt) {P : W →ₗ[ℝ] LinearMap.ker B}
    (hP : ∀ k : LinearMap.ker B, P k = k) (hρ : IsInvariantForm ρ ω.toBilinForm)
    (hσ : IsInvariantForm σ B) (hισ : ∀ g w, ι (σ g w) = ρ g (ι w))
    (hPσ : ∀ g w, (P (σ g w) : W) = σ g (P w))
    {πV : Representation ℝ G (ω.ReducedSpace (ω.orthogonal (LinearMap.range ι)))}
    (hπV : ∀ g (u u' : ω.orthogonal (LinearMap.range ι)), (u' : E) = ρ g u →
      πV g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u') :
    IsInvariantForm ((σ.prod hσ.kerRepresentation.dual).prod πV)
      ((hB.coisotropicModel P hP).prod
        (ω.reduction (ω.orthogonal (LinearMap.range ι)))).toBilinForm := by
  have hρ' (g : G) (u v : E) : ω (ρ g u) (ρ g v) = ω u v := hρ.apply g u v
  have hV := isInvariantForm_reduction hρ'
    (fun g _ hu ↦ apply_mem_orthogonal_range hρ' hισ g hu) hπV
  refine isInvariantForm_iff.2 fun g ⟨x, v⟩ ⟨x', v'⟩ ↦ ?_
  simpa [hV.apply g v v'] using (hB.isInvariantForm_coisotropicModel hP hσ hPσ).apply g x x'

/-- **The equivariant presymplectic Witt extension.** Let `G` act on a finite-dimensional
symplectic vector space `(E, ω)` by a semisimple representation `ρ` preserving `ω`, and on `W` by
`σ`. Let `ι : W → E` be an injective equivariant linear map pulling `ω` back to the alternating
form `B`, with kernel `K`, and let `P : W → K` be an equivariant projection. Let `G` act on the
reduced space `V = (ι W)^ω ⧸ (ι W ∩ (ι W)^ω)` by `πV`, `[u] ↦ [ρ g u]`. Then `ι` extends to an
equivariant linear symplectomorphism

`(W × K*) × V ≃ E`, `((w, 0), 0) ↦ ι w`,

from the direct sum of the coisotropic model on `W × K*` and `V`, which maps each `((0, 0), v)` to
a vector of `(ι W)^ω` with class `v`, so that it identifies `V` with an invariant complement of the
radical. The group acts on the model through `σ` on `W`, the dual of its restriction to `K` on `K*`
and `πV` on `V`. A continuous finite-dimensional representation of a compact group is semisimple
(`Representation.isSemisimpleRepresentation_of_continuous`). -/
theorem exists_equivariant_isSymplectomorphism_coisotropicModel_prod_reduction
    [FiniteDimensional ℝ E] [ρ.IsSemisimpleRepresentation] (hB : B.IsAlt)
    {P : W →ₗ[ℝ] LinearMap.ker B} (hP : ∀ k : LinearMap.ker B, P k = k)
    (hρ : IsInvariantForm ρ ω.toBilinForm)
    (hσ : IsInvariantForm σ B) (hι : Function.Injective ι)
    (hω : ∀ w w', ω (ι w) (ι w') = B w w') (hισ : ∀ g w, ι (σ g w) = ρ g (ι w))
    (hPσ : ∀ g w, (P (σ g w) : W) = σ g (P w))
    {πV : Representation ℝ G (ω.ReducedSpace (ω.orthogonal (LinearMap.range ι)))}
    (hπV : ∀ g (u u' : ω.orthogonal (LinearMap.range ι)), (u' : E) = ρ g u →
      πV g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u') :
    ∃ e : ((W × Dual ℝ (LinearMap.ker B)) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ι)))
        ≃ₗ[ℝ] E,
      IsSymplectomorphism ((hB.coisotropicModel P hP).prod (ω.reduction _)) ω e ∧
        (∀ w, e ((w, 0), 0) = ι w) ∧
        (∀ v, ∃ hv : e ((0, 0), v) ∈ ω.orthogonal (LinearMap.range ι),
          Submodule.Quotient.mk ⟨_, hv⟩ = v) ∧
        ∀ g x, e (((σ.prod hσ.kerRepresentation.dual).prod πV) g x) = ρ g (e x) := by
  have : FiniteDimensional ℝ W := .of_injective ι hι
  have hρ' (g : G) (u v : E) : ω (ρ g u) (ρ g v) = ω u v := hρ.apply g u v
  obtain ⟨s, hs, hsπ⟩ := exists_equivariant_lift_reducedSpace hρ'
    (fun g _ hu ↦ apply_mem_orthogonal_range hρ' hισ g hu) hπV
  -- `F` embeds `W × V` into `E` and `J` into the model; both pull back `B ⊕ ω_V`.
  let F := ι.coprod ((ω.orthogonal (LinearMap.range ι)).subtype ∘ₗ s)
  let J := (LinearMap.inl ℝ W (Dual ℝ (LinearMap.ker B))).prodMap
    (LinearMap.id : ω.ReducedSpace (ω.orthogonal (LinearMap.range ι)) →ₗ[ℝ] _)
  have hF (w : W) (v : ω.ReducedSpace (ω.orthogonal (LinearMap.range ι))) :
      F (w, v) = ι w + s v := rfl
  -- The model representation is semisimple: `W`, `V` and `K` embed into `E`, and `K*` is the
  -- dual of `K`.
  have : σ.IsSemisimpleRepresentation :=
    (ι.intertwiningMap_of_isIntertwiningMap σ ρ hισ).isSemisimpleRepresentation_of_injective hι
  have : πV.IsSemisimpleRepresentation :=
    (((ω.orthogonal (LinearMap.range ι)).subtype ∘ₗ s).intertwiningMap_of_isIntertwiningMap πV ρ
      hsπ).isSemisimpleRepresentation_of_injective
      ((Submodule.injective_subtype _).comp (Function.LeftInverse.injective hs))
  have : hσ.kerRepresentation.IsSemisimpleRepresentation :=
    ((ι ∘ₗ (LinearMap.ker B).subtype).intertwiningMap_of_isIntertwiningMap hσ.kerRepresentation ρ
      fun g k ↦ by simp [hισ]).isSemisimpleRepresentation_of_injective
      fun _ _ h ↦ Subtype.ext (hι h)
  obtain ⟨e, he, heJ, heρ⟩ := exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic
    (isInvariantForm_model hB hP hρ hσ hισ hPσ hπV) hρ (ι₁ := J) (ι₂ := F) (σ := σ.prod πV)
    (fun _ _ h ↦ Prod.ext_iff.2 (by simpa [J] using h))
    (injective_coprod_subtype_comp hι le_rfl hs)
    (fun ⟨w, v⟩ ⟨w', v'⟩ ↦ by
      have h₁ := ω.isRefl.eq_zero ((s v).property _ ⟨w', rfl⟩)
      have h₂ := (s v').property _ ⟨w, rfl⟩
      have h₃ : ω (s v) (s v') = ω.reduction _ v v' := by
        conv_rhs => rw [← hs v, ← hs v']
        exact (reduction_mk ω _ _ _).symm
      beta_reduce at h₃
      simp only [hF, map_add, LinearMap.add_apply, hω, h₁, h₂, h₃]
      simp [J])
    (by
      rw [LinearMap.range_prodMap, LinearMap.range_id]
      exact IsCoisotropic.prod (hB.isCoisotropic_range_inl_coisotropicModel hP) isCoisotropic_top)
    (by rw [LinearMap.range_coprod]; exact isCoisotropic_sup_range_subtype_comp hs)
    (fun g ⟨w, v⟩ ↦ by simp [J])
    (fun g ⟨w, v⟩ ↦ by simp [hF, hισ, hsπ])
  have he₀ (w : W) (v : ω.ReducedSpace (ω.orthogonal (LinearMap.range ι))) :
      e ((w, 0), v) = ι w + s v :=
    heJ (w, v)
  refine ⟨e, he, fun w ↦ by simp [he₀], fun v ↦ ⟨by simp [he₀], ?_⟩, heρ⟩
  conv_rhs => rw [← hs v]
  congr 1
  ext
  simp [he₀]

end LinearMap.BilinForm.IsAlt
