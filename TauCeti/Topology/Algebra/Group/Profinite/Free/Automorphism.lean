/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Surjective

/-!
# Continuous automorphisms of a free pro-`p` group of finite rank

Let `F` be a topological group with a topological isomorphism `e : F ≃ₜ* freeProP p X` to the free
pro-`p` group on a finite type `X`, so that `x i := e.symm (freeProP.of i)` is a basis of `F`.
A continuous automorphism of `F` is prescribed by its values on the basis, and any family of values
that topologically generates `F` is attained: the endomorphism `x i ↦ y i` given by the universal
property is surjective, hence bijective by the Hopf property of topologically finitely generated
profinite groups.

The main source of such families is the following: if each `y i` is a conjugate of the `p`-adic
power of `x i` by a unit `u i`, then the `y i` generate by Burnside's basis theorem, since modulo
the Frattini subgroup conjugation is trivial and `x i ^ u i` generates the same closed subgroup as
`x i`. So for every family of units `u i` and every choice of conjugators `c i` there is a
continuous automorphism with `x i ↦ (c i)⁻¹ * x i ^ u i * c i`. This is the automorphism criterion
by which endomorphisms of a free pro-`p` group given on a basis by conjugated unit powers, such as
the automorphisms of free pro-`p` groups preserving the peripheral conjugacy classes up to a common
exponent, are shown to be automorphisms.

## Main results

* `TauCeti.freeProP.exists_continuousAut_of_topologicallyGenerates`: every topological generating
  family of `F` indexed by `X` is the image of the basis under a continuous automorphism.
* `TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow`: for every family of units `u` and
  every family of conjugators `c`, some continuous automorphism of `F` sends `x i` to
  `(c i)⁻¹ * x i ^ u i * c i`.
* `TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow_const`: the special case of a common
  unit `u`, sending `x i` to `(c i)⁻¹ * x i ^ u * c i`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Proposition 2.5.2 (the Hopf property)
  and Proposition 2.8.7 (Burnside's basis theorem).
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} {X : Type u}

namespace freeProP

variable [Finite X]

/-- **Generating families are images of the basis under automorphisms.** If `F` is a free pro-`p`
group on the finite type `X`, with basis `x i := e.symm (of i)`, then every family `y : X → F`
that topologically generates `F` is the image of the basis under a continuous automorphism of
`F`. -/
theorem exists_continuousAut_of_topologicallyGenerates {F : Type v} [Group F] [TopologicalSpace F]
    [IsTopologicalGroup F] (e : F ≃ₜ* freeProP p X) {y : X → F}
    (hy : (Subgroup.closure (Set.range y)).topologicalClosure = ⊤) :
    ∃ φ : ContinuousAut F, ∀ i, φ (e.symm (of i)) = y i := by
  have hey : (Subgroup.closure (Set.range (e ∘ y))).topologicalClosure = ⊤ := by
    rw [Set.range_comp]
    exact topologicalClosure_closure_image_eq_top hy (f := (e : F →* freeProP p X))
      e.continuous e.surjective.denseRange
  refine ⟨e.trans ((continuousMulEquivOfTopologicallyGenerates (e ∘ y) hey).trans e.symm),
    fun i ↦ ?_⟩
  simp

end freeProP

namespace IsProP

variable [Fact p.Prime] [Finite X]

/-- **The automorphism criterion for conjugated unit powers.** If `F` is a free pro-`p` group on
the finite type `X`, with basis `x i := e.symm (freeProP.of i)`, then for every family of units
`u : X → ℤ_[p]ˣ` and every family of conjugators `c : X → F` there is a continuous automorphism of
`F` sending each `x i` to `(c i)⁻¹ * x i ^ u i * c i`. -/
theorem exists_continuousAut_apply_eq_conj_padicPow {F : Type v} [Group F] [TopologicalSpace F]
    [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p X) (u : X → ℤ_[p]ˣ) (c : X → F) :
    ∃ φ : ContinuousAut F, ∀ i,
      φ (e.symm (freeProP.of i)) = (c i)⁻¹ * hF.padicPow (e.symm (freeProP.of i)) (u i) * c i := by
  -- The basis generates `F`, being the image of the generators of `freeProP p X` under `e.symm`.
  have hx := topologicalClosure_closure_image_eq_top
    (freeProP.topologicalClosure_closure_range_of_eq_top p X)
    (f := (e.symm : freeProP p X →* F)) e.symm.continuous e.symm.surjective.denseRange
  rw [← Set.range_comp] at hx
  -- `hx` is stated for `⇑(e.symm : freeProP p X →* F) ∘ freeProP.of`, which is the basis by
  -- unfolding the coercion; `x` is given explicitly to keep the conclusion in basis form.
  exact freeProP.exists_continuousAut_of_topologicallyGenerates e <|
    hF.topologicalClosure_closure_range_eq_top_of_isConj_padicPow
      (x := fun i ↦ e.symm (freeProP.of i)) hx u fun i ↦
      isConj_iff.mpr ⟨(c i)⁻¹, by rw [inv_inv]⟩

/-- **The automorphism criterion for conjugated powers with a common unit.** The special case of
`exists_continuousAut_apply_eq_conj_padicPow` in which every basis element `x i` is raised to the
same unit `u` of `ℤ_[p]`: some continuous automorphism of `F` sends each `x i` to
`(c i)⁻¹ * x i ^ u * c i`. -/
theorem exists_continuousAut_apply_eq_conj_padicPow_const {F : Type v} [Group F]
    [TopologicalSpace F] [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]
    (hF : IsProP p F) (e : F ≃ₜ* freeProP p X) (u : ℤ_[p]ˣ) (c : X → F) :
    ∃ φ : ContinuousAut F, ∀ i,
      φ (e.symm (freeProP.of i)) = (c i)⁻¹ * hF.padicPow (e.symm (freeProP.of i)) u * c i :=
  hF.exists_continuousAut_apply_eq_conj_padicPow e (fun _ ↦ u) c

end IsProP

end TauCeti
