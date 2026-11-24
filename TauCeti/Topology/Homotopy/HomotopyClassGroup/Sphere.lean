/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import TauCeti.Topology.Homotopy.HomotopyClassGroup.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalMonoid

/-!
# Free homotopy classes of maps from a sphere into a topological group

Let `G` be a topological group, `Sⁿ` the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))` with
its north pole `N` (`TauCeti.sphereNorthPole`), and `[Sⁿ, G]` the group of free homotopy classes
of maps `Sⁿ → G` under pointwise multiplication (`TauCeti.HomotopyClassGroup`). Write `π₀(G)` for
`G ⧸ G₀`, the quotient by the path component of the identity.

For `n ≥ 1`, sending the class of a generalized loop `p` at `1` to the class of the corresponding
map `Sⁿ → G` (`GenLoop.toSphere`) is a homomorphism `πₙ(G, 1) →* [Sⁿ, G]`
(`TauCeti.HomotopyClassGroup.ofHomotopyGroup`): in a topological group the product of `πₙ` is the
pointwise product, by the Eckmann–Hilton argument (`HomotopyGroup.map_mul_prod`). It is injective,
because based maps that are freely homotopic are homotopic relative to `N`, and its image is the
kernel of evaluation at `N`. Evaluation at `N` is split by constant maps. So

`1 → πₙ(G, 1) → [Sⁿ, G] → π₀(G) → 1`

is a split extension of groups (`TauCeti.HomotopyClassGroup.sphereGroupExtension`,
`TauCeti.HomotopyClassGroup.sphereSplitting`), and `[Sⁿ, G]` is the semidirect product
`πₙ(G, 1) ⋊ π₀(G)` (`TauCeti.HomotopyClassGroup.sphereMulEquiv`), for the left action of `π₀(G)`
on `πₙ(G, 1)` by pointwise conjugation `[g] · [α] = [g α g⁻¹]`
(`TauCeti.HomotopyClassGroup.sphereSplitting_conjAct`). The decomposition of the class of `f` is
`([z ↦ f z (f N)⁻¹], [f N])` (`TauCeti.HomotopyClassGroup.sphereMulEquiv_symm_mk`).

For `n = 0` the sphere `S⁰` is the discrete space `{N, -N}`, and
`[S⁰, G] ≃* π₀(G) × π₀(G)` by evaluation at both points
(`TauCeti.HomotopyClassGroup.sphereZeroMulEquiv`).

These are the free homotopy classes of clutching functions: principal `G`-bundles over `Sⁿ⁺¹` are
glued from trivial bundles over the two hemispheres along a map `Sⁿ → G`.

## Main definitions

* `TauCeti.HomotopyClassGroup.ofHomotopyGroup n G : πₙ(G, 1) →* [Sⁿ, G]`.
* `TauCeti.HomotopyClassGroup.sphereGroupExtension n G`: the extension
  `1 → πₙ(G, 1) → [Sⁿ, G] → π₀(G) → 1`.
* `TauCeti.HomotopyClassGroup.sphereSplitting n G`: its splitting by constant maps.
* `TauCeti.HomotopyClassGroup.sphereMulEquiv n G : πₙ(G, 1) ⋊ π₀(G) ≃* [Sⁿ, G]`.
* `TauCeti.HomotopyClassGroup.sphereZeroMulEquiv G : [S⁰, G] ≃* π₀(G) × π₀(G)`.

## Main results

* `TauCeti.HomotopyClassGroup.ofHomotopyGroup_injective`,
  `TauCeti.HomotopyClassGroup.range_ofHomotopyGroup`: exactness on the left and in the middle.
* `TauCeti.HomotopyClassGroup.sphereSplitting_conjAct`: `π₀(G)` acts by pointwise conjugation.
* `TauCeti.HomotopyClassGroup.sphereMulEquiv_symm_mk`: the decomposition of a class.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer
  (1978), Chapter III, §5.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Proposition 1.11 and its proof (clutching
  functions up to homotopy).
-/

public section

open Metric ContinuousMap
open scoped Topology.Homotopy

namespace TauCeti.HomotopyClassGroup

section Positive

variable (n : ℕ) [NeZero n] {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The free homotopy class of the map `Sⁿ → G` of a class of `πₙ(G, 1)`, the function underlying
`TauCeti.HomotopyClassGroup.ofHomotopyGroup`. -/
private noncomputable def ofHomotopyGroupFun :
    HomotopyGroup (Fin n) G 1 →
      HomotopyClassGroup (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) G :=
  Quotient.lift (fun p ↦ mk _ G (GenLoop.toSphere p)) fun _ _ h ↦
    mk_eq_mk_iff.2 (GenLoop.homotopic_iff_toSphere.1 h).homotopic

variable (G) in
/-- The homomorphism `πₙ(G, 1) →* [Sⁿ, G]` sending the class of a generalized loop `p` at `1` to
the free homotopy class of the corresponding map `GenLoop.toSphere p : Sⁿ → G`. It is a
homomorphism because the product of `πₙ(G, 1)` is the pointwise product. -/
noncomputable def ofHomotopyGroup :
    HomotopyGroup (Fin n) G 1 →*
      HomotopyClassGroup (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) G where
  toFun := ofHomotopyGroupFun n
  map_one' := by
    rw [← HomotopyGroup.mk_const_eq_one]
    exact (congrArg (mk _ G) GenLoop.toSphere_const).trans (map_one _)
  map_mul' a b := by
    -- In a topological group the product of classes is the class of the pointwise product.
    have hid (a : HomotopyGroup (Fin n) G 1) :
        HomotopyGroup.map (y := 1) (ContinuousMap.id G) rfl a = a :=
      HomotopyGroup.map_id_apply a
    have h := HomotopyGroup.map_mul_prod (N := Fin n) (ContinuousMap.id G) (ContinuousMap.id G)
      (id_apply 1) (id_apply 1) a b
    rw [hid, hid] at h
    rw [← h]
    induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
    have hpq : GenLoop.toSphere (GenLoop.map (y := 1)
        ((ContinuousMap.id G).comp ContinuousMap.fst * (ContinuousMap.id G).comp ContinuousMap.snd)
        (by simp) (GenLoop.prod p q)) = GenLoop.toSphere p * GenLoop.toSphere q := by
      ext
      simp
    simp only [HomotopyGroup.prod_mk, HomotopyGroup.map_mk]
    exact (congrArg (mk _ G) hpq).trans (map_mul _ _ _)

@[simp]
theorem ofHomotopyGroup_mk (p : Ω^ (Fin n) G 1) :
    ofHomotopyGroup n G ⟦p⟧ = mk _ G (GenLoop.toSphere p) :=
  (rfl)

/-- **Exactness on the left**: based maps out of the sphere that are freely homotopic are
homotopic relative to the north pole, so `πₙ(G, 1) →* [Sⁿ, G]` is injective. -/
theorem ofHomotopyGroup_injective : Function.Injective (ofHomotopyGroup n G) := by
  intro a b hab
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  rw [ofHomotopyGroup_mk, ofHomotopyGroup_mk,
    mk_eq_mk_iff_homotopicRel (q := sphereNorthPole n) (by simp)] at hab
  exact Quotient.sound (GenLoop.homotopic_iff_toSphere.2 hab)

/-- **Exactness in the middle**: the image of `πₙ(G, 1)` in `[Sⁿ, G]` is the kernel of evaluation
at the north pole. -/
theorem range_ofHomotopyGroup :
    (ofHomotopyGroup n G).range = (eval G (sphereNorthPole n)).ker := by
  ext a
  rw [MonoidHom.mem_range, mem_ker_eval_iff]
  constructor
  · rintro ⟨b, rfl⟩
    induction b using Quotient.inductionOn with | h p =>
    exact ⟨GenLoop.toSphere p, by simp, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨⟦(GenLoop.sphereEquiv n G 1).symm ⟨f, hf⟩⟧, ?_⟩
    rw [ofHomotopyGroup_mk, ← GenLoop.coe_sphereEquiv_apply, Equiv.apply_symm_apply]

variable (G) in
/-- **The free homotopy classes of maps `Sⁿ → G` as an extension**: for `n ≥ 1` the sequence
`1 → πₙ(G, 1) → [Sⁿ, G] → π₀(G) → 1`, the second map induced by `GenLoop.toSphere` and the third
by evaluation at the north pole, is exact. -/
noncomputable def sphereGroupExtension :
    GroupExtension (HomotopyGroup (Fin n) G 1)
      (HomotopyClassGroup (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) G)
      (G ⧸ Subgroup.pathComponentOne G) where
  inl := ofHomotopyGroup n G
  rightHom := eval G (sphereNorthPole n)
  inl_injective := ofHomotopyGroup_injective n
  range_inl_eq_ker_rightHom := range_ofHomotopyGroup n
  rightHom_surjective := eval_surjective _

@[simp]
theorem sphereGroupExtension_inl : (sphereGroupExtension n G).inl = ofHomotopyGroup n G :=
  (rfl)

@[simp]
theorem sphereGroupExtension_rightHom :
    (sphereGroupExtension n G).rightHom = eval G (sphereNorthPole n) :=
  (rfl)

variable (G) in
/-- The splitting of `1 → πₙ(G, 1) → [Sⁿ, G] → π₀(G) → 1` by the classes of constant maps. -/
noncomputable def sphereSplitting : (sphereGroupExtension n G).Splitting where
  toMonoidHom := const _
  rightInverse_rightHom := eval_const _

@[simp]
theorem sphereSplitting_apply (a : G ⧸ Subgroup.pathComponentOne G) :
    sphereSplitting n G a = const _ a :=
  (rfl)

/-- **The action of `π₀(G)` on `πₙ(G, 1)` in the split extension is pointwise conjugation**:
`[g] · α = [g α g⁻¹]`, the image of `α` under the conjugation `x ↦ g * x * g⁻¹` of `G`. -/
@[simp]
theorem sphereSplitting_conjAct (g : G) (a : HomotopyGroup (Fin n) G 1) :
    (sphereSplitting n G).conjAct (g : G ⧸ Subgroup.pathComponentOne G) a =
      HomotopyGroup.map ⟨fun x ↦ g * x * g⁻¹, by fun_prop⟩ (by simp) a := by
  apply ofHomotopyGroup_injective n
  -- In the extension, the action is conjugation by the class of the constant map at `g`.
  have hconj (a : G ⧸ Subgroup.pathComponentOne G) (b : HomotopyGroup (Fin n) G 1) :
      ofHomotopyGroup n G ((sphereSplitting n G).conjAct a b) =
        sphereSplitting n G a * ofHomotopyGroup n G b * (sphereSplitting n G a)⁻¹ :=
    (sphereGroupExtension n G).inl_conjAct_comm
  rw [hconj]
  induction a using Quotient.inductionOn with | h p =>
  have h : ContinuousMap.const _ g * GenLoop.toSphere p * (ContinuousMap.const _ g)⁻¹ =
      GenLoop.toSphere (GenLoop.map (y := 1) ⟨fun x ↦ g * x * g⁻¹, by fun_prop⟩ (by simp) p) := by
    rw [GenLoop.toSphere_map]
    ext
    simp
  simpa using congrArg (mk _ G) h

variable (G) in
/-- **`[Sⁿ, G]` is a semidirect product**: for `n ≥ 1`,
`πₙ(G, 1) ⋊ π₀(G) ≃* [Sⁿ, G]`, `(α, [g]) ↦ α · [g]`, where `π₀(G)` acts on `πₙ(G, 1)` by pointwise
conjugation (`TauCeti.HomotopyClassGroup.sphereSplitting_conjAct`). -/
noncomputable def sphereMulEquiv :
    HomotopyGroup (Fin n) G 1 ⋊[(sphereSplitting n G).conjAct]
        (G ⧸ Subgroup.pathComponentOne G) ≃*
      HomotopyClassGroup (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) G :=
  (sphereSplitting n G).semidirectProductMulEquiv

/-- The pair `(α, a)` corresponds to the product of `α ∈ πₙ(G, 1)` with the class of a constant
map in the path component `a`. -/
@[simp]
theorem sphereMulEquiv_apply
    (x : HomotopyGroup (Fin n) G 1 ⋊[(sphereSplitting n G).conjAct]
      (G ⧸ Subgroup.pathComponentOne G)) :
    sphereMulEquiv n G x = ofHomotopyGroup n G x.left * const _ x.right :=
  (rfl)

/-- **The decomposition of a class in `[Sⁿ, G]`**: the class of `f` corresponds to the pair of the
class of the based map `z ↦ f z * (f N)⁻¹` in `πₙ(G, 1)` and the path component of `f N`. -/
@[simp]
theorem sphereMulEquiv_symm_mk (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, G)) :
    (sphereMulEquiv n G).symm (mk _ G f) =
      ⟨⟦(GenLoop.sphereEquiv n G 1).symm
          ⟨f * ContinuousMap.const _ (f (sphereNorthPole n))⁻¹, by simp⟩⟧,
        (f (sphereNorthPole n) : G ⧸ Subgroup.pathComponentOne G)⟩ := by
  rw [MulEquiv.symm_apply_eq, sphereMulEquiv_apply, ofHomotopyGroup_mk,
    ← GenLoop.coe_sphereEquiv_apply, Equiv.apply_symm_apply, const_mk, ← map_mul]
  congr 1
  ext
  simp

end Positive

section Zero

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

variable (G) in
/-- **Homotopy classes of maps out of the zero-sphere**: `[S⁰, G] ≃* π₀(G) × π₀(G)`, the class of
`f` going to the path components of its values at the north pole and at its antipode. -/
noncomputable def sphereZeroMulEquiv :
    HomotopyClassGroup (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) G ≃*
      (G ⧸ Subgroup.pathComponentOne G) × (G ⧸ Subgroup.pathComponentOne G) :=
  haveI := discreteTopology_sphere_of_finrank_eq_one finrank_euclideanSpace_fin
    (0 : EuclideanSpace ℝ (Fin 1)) 1
  (piMulEquivOfDiscrete _ G).trans <| MulEquiv.ofBijective
    ((Pi.evalMonoidHom _ (sphereNorthPole 0)).prod (Pi.evalMonoidHom _ (-sphereNorthPole 0))) <| by
      refine ⟨fun φ ψ h ↦ funext fun t ↦ ?_, fun ab ↦ ⟨fun t ↦ if t = sphereNorthPole 0 then ab.1
        else ab.2, ?_⟩⟩
      · simp only [MonoidHom.prod_apply, Pi.evalMonoidHom_apply, Prod.mk.injEq] at h
        -- `S⁰` consists of the north pole and its antipode.
        have ht : (t : EuclideanSpace ℝ (Fin 1)) ∈ ({(sphereNorthPole 0 : EuclideanSpace ℝ (Fin 1)),
            -(sphereNorthPole 0 : EuclideanSpace ℝ (Fin 1))} : Set _) :=
          sphere_eq_pair_of_finrank_eq_one finrank_euclideanSpace_fin
            (sphereNorthPole 0).property ▸ t.property
        rcases ht with ht | ht
        · rw [show t = sphereNorthPole 0 from Subtype.ext ht]
          exact h.1
        · rw [show t = -sphereNorthPole 0 from Subtype.ext ht]
          exact h.2
      · simp [(ne_neg_of_mem_unit_sphere ℝ (sphereNorthPole 0)).symm]

@[simp]
theorem sphereZeroMulEquiv_mk (f : C(sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, G)) :
    sphereZeroMulEquiv G (mk _ G f) =
      ((f (sphereNorthPole 0) : G ⧸ Subgroup.pathComponentOne G),
        (f (-sphereNorthPole 0) : G ⧸ Subgroup.pathComponentOne G)) :=
  haveI := discreteTopology_sphere_of_finrank_eq_one finrank_euclideanSpace_fin
    (0 : EuclideanSpace ℝ (Fin 1)) 1
  Prod.ext (piMulEquivOfDiscrete_mk f _) (piMulEquivOfDiscrete_mk f _)

end Zero

end TauCeti.HomotopyClassGroup
