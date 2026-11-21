/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.NTQ.Cover
import TauCeti.GroupTheory.Commutator
import TauCeti.GroupTheory.GroupAlgGeom.Abelian
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Tower covers over an abelian base

Let `G` be a torsion-free abelian group, such as `ℤ`, a free group of rank at most one, or any
abelian fully residually free group. The solution set of a system `S` over `G` in finitely many
variables has a finite cover by normalized towers over `G` discriminated by `G`, in the sense of
`TauCeti.LimitGroup.NTQ.TowerCover`: every solution of `S` is `ψ ∘ θ_j ∘ (x ↦ x)` for one of the
towers `T_j`, its homomorphism `θ_j : G_{R(S)} → T_j` over `G` from the coordinate group of `S`,
and a homomorphism `ψ : T_j → G` over `G`.

## Main results

* `TauCeti.LimitGroup.NTQ.exists_towerCover_of_isMulCommutative`: over a torsion-free abelian
  group, the solution set of a system in finitely many variables has a cover by normalized towers
  discriminated by the group.

## Implementation notes

If `S` has a solution, its coordinate group is `G × ℤᵏ` over `G`
(`TauCeti.GroupAlgGeom.CoordGroup.exists_bijective_gHom_prod_of_isMulCommutative`). It maps over
`G` to the carrier `T` of the quadratic level `[x₀, y₀] ⋯ [xₖ, yₖ] = 1` over `G`, the basis
vectors of `ℤᵏ` going to `x₀, …, x_{k-1}`. Every tuple of `G` solves that equation, so every
homomorphism `G × ℤᵏ → G` over `G` factors through `T`. The carrier `T` is separated by `G`,
hence abelian and discriminated by `G`
(`TauCeti.GroupAlgGeom.IsSeparatedBy.isDiscriminatedBy_of_commGroup`).

## References

* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §0, Theorem 2 (the finite covers of solution sets, over a nonabelian free
  group; this file treats an abelian base).
-/

public section

open TauCeti.GroupAlgGeom

universe u

namespace TauCeti.LimitGroup.NTQ

variable {G : Type u} [Group G]

/-- The standard quadratic equation `[x₀, y₀] ⋯ [xₖ, yₖ] = 1` of genus `k + 1` over `G`. -/
private def commEquation (k : ℕ) : Quadratic.Standard G (ULift.{u} (Fin (k + 1) ⊕ Fin (k + 1))) :=
  .orientable (k + 1) k.succ_pos (ULift.up ∘ .inl) (ULift.up ∘ .inr) <|
    (ULift.up_injective.comp Sum.inl_injective).sumElim (ULift.up_injective.comp Sum.inr_injective)
      fun _ _ h ↦ Sum.inl_ne_inr (ULift.up_injective h)

open scoped IsMulCommutative

/-- Over a torsion-free abelian group `G`, for every `k` there are a normalized tower over `G`
whose top carrier `T` is abelian and discriminated by `G`, and `q : Fin k → T` such that every
`t : Fin k → G` is the image of `q` under a homomorphism `T → G` over `G`. -/
private theorem exists_tower_isDiscriminatedBy [IsMulCommutative G] [IsMulTorsionFree G] (k : ℕ) :
    ∃ (T : Type u) (_ : Group T) (j : G →* T) (_ : Tower G T j) (q : Fin k → T),
      IsDiscriminatedBy j (MonoidHom.id G) ∧ IsMulCommutative T ∧
        ∀ t : Fin k → G, ∃ ρ : GHom j (MonoidHom.id G), ⇑ρ ∘ q = t := by
  -- Over an abelian group every tuple solves `[x₀, y₀] ⋯ [xₖ, yₖ] = 1`.
  have hV (v : ULift.{u} (Fin (k + 1) ⊕ Fin (k + 1)) → G) :
      v ∈ V (MonoidHom.id G) {(commEquation k).toWord} :=
    Quadratic.Standard.mem_V_orientable_of_commute _ _ _ fun _ ↦ mul_comm' _ _
  have hsep := CoordGroup.isSeparatedBy_coeff (ι := MonoidHom.id G) {(commEquation k).toWord}
  -- The carrier of the quadratic level is the coordinate group of the equation, with its
  -- coefficient map (`TowerLevel.inclusion_quadratic`).
  refine ⟨CoordGroup (MonoidHom.id G) {(commEquation k).toWord}, inferInstance,
    CoordGroup.coeff _ _, Tower.single (.quadratic _ (commEquation k) 1 (hV 1)),
    fun i ↦ CoordGroup.genericPoint _ _ ⟨.inl i.castSucc⟩,
    hsep.isDiscriminatedBy_of_commGroup ⟨CoordGroup.evalGHom 1 (hV 1)⟩,
    isMulCommutative_of_forall_exists_monoidHom_apply_ne_one (A := G) fun g hg ↦ ?_, fun t ↦
      ⟨CoordGroup.evalGHom _ (hV fun y ↦ Sum.elim (Fin.snoc t 1) 1 y.down),
        funext fun i ↦ by simp⟩⟩
  obtain ⟨φ, hφ⟩ := (isSeparatedBy_def _ _).1 hsep g hg
  exact ⟨φ, hφ⟩

/-- For an abelian group `T` over `G` and `q : Fin k → T`, the homomorphism `G × ℤᵏ → T` over
`G` sending the `i`-th basis vector of `ℤᵏ` to `q i`. -/
private def prodGHom {T : Type u} [Group T] [IsMulCommutative T] (j : G →* T) {k : ℕ}
    (q : Fin k → T) : GHom (MonoidHom.inl G (Fin k → Multiplicative ℤ)) j :=
  ⟨j.coprod (zpowersPiHom q fun _ _ ↦ .all _ _), fun g ↦ by simp⟩

/-- If every tuple `t : Fin k → G` is `ρ ∘ q` for a homomorphism `ρ : T → G` over `G`, then every
homomorphism `G × ℤᵏ → G` over `G` factors through `prodGHom j q`. -/
private theorem exists_gHom_comp_prodGHom [IsMulCommutative G] {T : Type u} [Group T]
    [IsMulCommutative T] {j : G →* T} {k : ℕ} {q : Fin k → T}
    (hq : ∀ t : Fin k → G, ∃ ρ : GHom j (MonoidHom.id G), ⇑ρ ∘ q = t)
    (φ : GHom (MonoidHom.inl G (Fin k → Multiplicative ℤ)) (MonoidHom.id G)) :
    ∃ ρ : GHom j (MonoidHom.id G), ρ.comp (prodGHom j q) = φ := by
  obtain ⟨ρ, hρ⟩ := hq fun i ↦ φ (1, Pi.mulSingle i (.ofAdd 1))
  -- `ρ ∘ prodGHom j q` and `φ` agree on the basis vectors of `ℤᵏ`, and both fix `G`.
  have h₂ : (ρ : T →* G).comp (zpowersPiHom q fun _ _ ↦ .all _ _) =
      (φ : G × (Fin k → Multiplicative ℤ) →* G).comp (MonoidHom.inr _ _) := by
    ext i
    simpa using congrFun hρ i
  have h : (ρ : T →* G).comp (j.coprod (zpowersPiHom q fun _ _ ↦ .all _ _)) = φ := by
    rw [← MonoidHom.coprod_unique (φ : G × (Fin k → Multiplicative ℤ) →* G),
      MonoidHom.comp_coprod, GHom.comp_coeff, GHom.comp_coeff, h₂]
  exact ⟨ρ, GHom.ext fun y ↦ by rw [GHom.coe_comp]; exact DFunLike.congr_fun h y⟩

/-- Over a torsion-free abelian group `G`, the solution set of every system in finitely many
variables has a cover by normalized towers discriminated by `G`. -/
theorem exists_towerCover_of_isMulCommutative [IsMulCommutative G] [IsMulTorsionFree G]
    {X : Type*} [Finite X] (S : Set (GX G X)) : ∃ c : TowerCover S (V (MonoidHom.id G) S),
      ∀ j, IsDiscriminatedBy (c.coeff j) (MonoidHom.id G) := by
  rcases (V (MonoidHom.id G) S).eq_empty_or_nonempty with hS | hS
  · -- No solution: the empty cover.
    exact ⟨⟨0, Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0,
      by simp [hS]⟩, fun j ↦ j.elim0⟩
  -- The coordinate group is `G × ℤᵏ`; it maps to the tower `T`, `eᵢ` going to `q i`.
  obtain ⟨k, f, hf⟩ := CoordGroup.exists_bijective_gHom_prod_of_isMulCommutative hS
  obtain ⟨T, _, j, t, q, hT, hTc, hq⟩ := exists_tower_isDiscriminatedBy (G := G) k
  refine ⟨⟨1, fun _ ↦ T, fun _ ↦ inferInstance, fun _ ↦ j, fun _ ↦ t,
    fun _ ↦ (prodGHom j q).comp f, fun v hv ↦ ?_⟩, fun _ ↦ hT⟩
  -- A solution `v` is `ev_v ∘ (x ↦ x)`, and `ev_v ∘ f⁻¹` factors through `prodGHom j q`.
  obtain ⟨ρ, hρ⟩ := exists_gHom_comp_prodGHom hq
    ((CoordGroup.evalGHom v hv).comp (f.symmOfBijective hf))
  refine Set.mem_iUnion.2 ⟨0, ρ, funext fun x ↦ ?_⟩
  simpa using DFunLike.congr_fun hρ (f (CoordGroup.genericPoint (MonoidHom.id G) S x))

end TauCeti.LimitGroup.NTQ
