/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialComplex.Acyclic

/-!
# Chain homotopies from cone carriers

Let `K` and `L` be simplicial complexes with linearly ordered vertices, and let `φ` and `ψ` be
chain maps between their ordered chain complexes, given degreewise by linear maps of ordered
chains, which agree after augmentation. A *cone carrier* for `φ` and `ψ` assigns to every face `σ`
of `K` a vertex `v σ` of `L` and a collection `P σ` of faces of `L` such that

* every face in `P σ` lies in the closed cone at `v σ`: its vertices are at most `v σ`, and
  adjoining `v σ` to it gives a face of `L`;
* `P σ` is closed under adjoining `v σ`;
* `P` is monotone: `P τ ⊆ P σ` whenever `τ ≤ σ`;
* `φ σ` and `ψ σ` are supported on `P σ`.

The chain complex of `P σ` is then acyclic, being a cone, and the classical acyclic carrier
theorem says that `φ` and `ψ` are chain homotopic. Here the homotopy is explicit: coning off at
`v σ` contracts the chains supported on `P σ`, and the operator
`TauCeti.OrderedSimplicialChain.carrierHomotopy` is defined by induction on the degree as

`D σ = -(φ σ - ψ σ) * v σ` for a vertex `σ`,  `D σ = (-1) ^ n (φ σ - ψ σ - D ∂σ) * v σ` for an
`(n + 1)`-cell `σ`,

where `z * w` is the cone operator `TauCeti.OrderedSimplicialChain.cone`. It is supported on the
carrier (`TauCeti.OrderedSimplicialChain.carrier_of_mem_support_carrierHomotopy`), and it satisfies
`∂ D = φ - ψ` in degree `0` and `∂ D + D ∂ = φ - ψ` in positive degrees, which gives the chain
homotopy `TauCeti.orderedSimplicialChainComplexHomotopyOfCarrier`.

The faces in `P σ` may contain the cone vertex `v σ` itself: when `ψ` is the identity, `P σ`
contains `σ`. Their cones vanish, and the cone identities
`TauCeti.OrderedSimplicialChain.boundary_cone_zero` and
`TauCeti.OrderedSimplicialChain.boundary_cone_succ` hold on the whole closed cone.

## Main definitions

* `TauCeti.OrderedSimplicialChain.carrierHomotopy`: the homotopy operator of a cone carrier.
* `TauCeti.orderedSimplicialChainComplexHomotopyOfCarrier`: the chain homotopy between two chain
  maps with a common cone carrier.

## Main results

* `TauCeti.OrderedSimplicialChain.carrier_of_mem_support_carrierHomotopy`: the homotopy operator
  is supported on the carrier.
* `TauCeti.OrderedSimplicialChain.boundary_comp_carrierHomotopy_zero`,
  `TauCeti.OrderedSimplicialChain.boundary_comp_carrierHomotopy_succ`: the homotopy identities.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984, §13, the acyclic carrier
  theorem.
* A. Hatcher, *Algebraic Topology*, Section 2.1, the proof that the subdivision operator is chain
  homotopic to the identity.
-/

public section

noncomputable section

open CategoryTheory Finsupp

open AbstractSimplicialComplex

namespace TauCeti

namespace OrderedSimplicialChain

variable {α ι : Type*} [LinearOrder α] [LinearOrder ι]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex ι}

section Def

variable (R : Type*) [Ring R]
  (φ ψ : ∀ n, OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n)
  (v : TauCeti.SetLike.Face K → ι)

/-- The **homotopy operator of a cone carrier** with cone vertices `v` between the degreewise maps
`φ` and `ψ` of ordered chains. A vertex `σ` goes to `-(φ σ - ψ σ) * v σ`, and an `(n + 1)`-cell `σ`
goes to `(-1) ^ n (φ σ - ψ σ - D ∂σ) * v σ`, where `z * w` is the cone operator. When `v` is part
of a cone carrier for chain maps `φ` and `ψ` agreeing after augmentation, this is a chain homotopy
between them (`boundary_comp_carrierHomotopy_zero`, `boundary_comp_carrierHomotopy_succ`). -/
def carrierHomotopy :
    (n : ℕ) → OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R (n + 1)
  | 0 => linearCombination R fun c ↦ -cone R (v c.val) 0 (φ 0 (single c 1) - ψ 0 (single c 1))
  | n + 1 => linearCombination R fun c ↦ (-1 : R) ^ n • cone R (v c.val) (n + 1)
      (φ (n + 1) (single c 1) - ψ (n + 1) (single c 1) -
        carrierHomotopy n (boundary R n (single c 1)))

variable {R φ ψ v}

/-- The homotopy operator of a cone carrier on a vertex `σ` is `-(φ σ - ψ σ) * v σ`. -/
theorem carrierHomotopy_zero_single (c : RealizationCell K 0) :
    carrierHomotopy R φ ψ v 0 (single c 1) =
      -cone R (v c.val) 0 (φ 0 (single c 1) - ψ 0 (single c 1)) := by
  simp [carrierHomotopy]

/-- The homotopy operator of a cone carrier on an `(n + 1)`-cell `σ` is
`(-1) ^ n (φ σ - ψ σ - D ∂σ) * v σ`. -/
theorem carrierHomotopy_succ_single {n : ℕ} (c : RealizationCell K (n + 1)) :
    carrierHomotopy R φ ψ v (n + 1) (single c 1) =
      (-1 : R) ^ n • cone R (v c.val) (n + 1)
        (φ (n + 1) (single c 1) - ψ (n + 1) (single c 1) -
          carrierHomotopy R φ ψ v n (boundary R n (single c 1))) := by
  simp [carrierHomotopy]

end Def

variable {R : Type*} [Ring R]
  {φ ψ : ∀ n, OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n}
  {v : TauCeti.SetLike.Face K → ι} {P : TauCeti.SetLike.Face K → Finset ι → Prop}

section Support

variable (hinsert : ∀ σ, ∀ s ∈ L, P σ s → P σ (insert (v σ) s))
  (hmono : ∀ ⦃τ σ : TauCeti.SetLike.Face K⦄, τ ≤ σ → ∀ s ∈ L, P τ s → P σ s)
  (hφ : ∀ n (c : RealizationCell K n), ∀ d ∈ (φ n (single c 1)).support, P c.val d.val.val)
  (hψ : ∀ n (c : RealizationCell K n), ∀ d ∈ (ψ n (single c 1)).support, P c.val d.val.val)

omit [LinearOrder α] in
include hφ hψ in
/-- The difference `φ σ - ψ σ` is supported on the carrier `P σ`. -/
private theorem carrier_of_mem_support_sub {n : ℕ} (c : RealizationCell K n)
    {e : RealizationCell L n} (he : e ∈ (φ n (single c 1) - ψ n (single c 1)).support) :
    P c.val e.val.val := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_sub he) with he | he
  exacts [hφ n c e he, hψ n c e he]

omit [LinearOrder α] in
include hinsert in
/-- Coning off at `v σ` keeps a chain supported on the carrier `P σ`. -/
private theorem carrier_of_mem_support_cone {σ : TauCeti.SetLike.Face K} {n : ℕ}
    {z : OrderedSimplicialChain L R n} (hz : ∀ e ∈ z.support, P σ e.val.val)
    {d : RealizationCell L (n + 1)} (hd : d ∈ (cone R (v σ) n z).support) : P σ d.val.val := by
  obtain ⟨e, he, -, -, rfl⟩ := exists_eq_cone_of_mem_support_cone hd
  rw [RealizationCell.cone_val]
  exact hinsert σ _ e.val.property (hz e he)

include hmono hφ hψ in
/-- The chain `φ σ - ψ σ - D ∂σ`, coned off in the homotopy operator on an `(n + 1)`-cell `σ`, is
supported on the carrier `P σ`. -/
private theorem carrier_of_mem_support_sub_carrierHomotopy_boundary {n : ℕ}
    (hD : ∀ (c : RealizationCell K n) (d : RealizationCell L (n + 1)),
      d ∈ (carrierHomotopy R φ ψ v n (single c 1)).support → P c.val d.val.val)
    (c : RealizationCell K (n + 1)) {e : RealizationCell L (n + 1)}
    (he : e ∈ (φ (n + 1) (single c 1) - ψ (n + 1) (single c 1) -
      carrierHomotopy R φ ψ v n (boundary R n (single c 1))).support) :
    P c.val e.val.val := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_sub he) with he | he
  · exact carrier_of_mem_support_sub hφ hψ c he
  · -- The cells of `D ∂σ` lie in the carriers of the faces of `σ`, hence in that of `σ`.
    obtain ⟨j, he⟩ := exists_mem_support_face_of_mem_support_boundary _ c he
    exact hmono (SetLike.face_le_iff.mpr (c.face_val_subset j)) _ e.val.property (hD _ _ he)

include hinsert hmono hφ hψ in
/-- **The homotopy operator of a cone carrier is supported on the carrier**: every cell in the
support of `D σ` lies in `P σ`. -/
theorem carrier_of_mem_support_carrierHomotopy (n : ℕ) (c : RealizationCell K n)
    {d : RealizationCell L (n + 1)} (hd : d ∈ (carrierHomotopy R φ ψ v n (single c 1)).support) :
    P c.val d.val.val := by
  induction n with
  | zero =>
    rw [carrierHomotopy_zero_single, Finsupp.support_neg] at hd
    exact carrier_of_mem_support_cone hinsert (fun _ ↦ carrier_of_mem_support_sub hφ hψ c) hd
  | succ n ih =>
    rw [carrierHomotopy_succ_single] at hd
    exact carrier_of_mem_support_cone hinsert
      (fun _ ↦ carrier_of_mem_support_sub_carrierHomotopy_boundary hmono hφ hψ
        (fun c _ ↦ ih c) c) (Finsupp.support_smul hd)

end Support

section Identities

variable (hcone : ∀ σ, ∀ s ∈ L, P σ s → (∀ w ∈ s, w ≤ v σ) ∧ insert (v σ) s ∈ L)
  (hinsert : ∀ σ, ∀ s ∈ L, P σ s → P σ (insert (v σ) s))
  (hmono : ∀ ⦃τ σ : TauCeti.SetLike.Face K⦄, τ ≤ σ → ∀ s ∈ L, P τ s → P σ s)
  (hφ : ∀ n (c : RealizationCell K n), ∀ d ∈ (φ n (single c 1)).support, P c.val d.val.val)
  (hψ : ∀ n (c : RealizationCell K n), ∀ d ∈ (ψ n (single c 1)).support, P c.val d.val.val)
  (hε : linearCombination R (fun _ : RealizationCell L 0 ↦ (1 : R)) ∘ₗ φ 0 =
      linearCombination R (fun _ : RealizationCell L 0 ↦ (1 : R)) ∘ₗ ψ 0)
  (hφd : ∀ n, boundary R n ∘ₗ φ (n + 1) = φ n ∘ₗ boundary R n)
  (hψd : ∀ n, boundary R n ∘ₗ ψ (n + 1) = ψ n ∘ₗ boundary R n)

include hcone hφ hψ hε in
/-- **The homotopy identity in degree `0`**: if `φ` and `ψ` agree after augmentation, then
`∂ D = φ - ψ` on `0`-chains. -/
theorem boundary_comp_carrierHomotopy_zero :
    boundary R 0 ∘ₗ carrierHomotopy R φ ψ v 0 = φ 0 - ψ 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  have hε' := congrArg (fun f ↦ f (single c 1)) hε
  simp only [LinearMap.coe_comp, Function.comp_apply] at hε'
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, LinearMap.sub_apply]
  rw [carrierHomotopy_zero_single, map_neg, boundary_cone_zero fun e he ↦
      hcone c.val _ e.val.property (carrier_of_mem_support_sub hφ hψ c he),
    map_sub, hε', sub_self, single_zero, zero_sub, neg_neg]

include hcone hinsert hmono hφ hψ in
/-- The homotopy identity in degree `n + 1`, given that `∂ D = φ - ψ` on the `n`-boundaries. -/
private theorem boundary_comp_carrierHomotopy_succ_of_boundary {n : ℕ}
    (hφd : boundary R n ∘ₗ φ (n + 1) = φ n ∘ₗ boundary R n)
    (hψd : boundary R n ∘ₗ ψ (n + 1) = ψ n ∘ₗ boundary R n)
    (hprev : ∀ y, boundary R n (carrierHomotopy R φ ψ v n (boundary R n y)) =
      φ n (boundary R n y) - ψ n (boundary R n y)) :
    boundary R (n + 1) ∘ₗ carrierHomotopy R φ ψ v (n + 1) +
        carrierHomotopy R φ ψ v n ∘ₗ boundary R n = φ (n + 1) - ψ (n + 1) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, lsingle_apply,
    LinearMap.sub_apply]
  -- The chain `z` coned off in `D σ` lies in the closed cone at `v σ`, and it is a cycle.
  obtain ⟨z, hz⟩ : ∃ z, z = φ (n + 1) (single c 1) - ψ (n + 1) (single c 1) -
      carrierHomotopy R φ ψ v n (boundary R n (single c 1)) := ⟨_, rfl⟩
  have hzP : ∀ e ∈ z.support, (∀ w ∈ e.val.val, w ≤ v c.val) ∧ insert (v c.val) e.val.val ∈ L :=
    fun e he ↦ hcone c.val _ e.val.property <| by
      rw [hz] at he
      exact carrier_of_mem_support_sub_carrierHomotopy_boundary hmono hφ hψ
        (fun c _ hd ↦ carrier_of_mem_support_carrierHomotopy hinsert hmono hφ hψ n c hd) c he
  have hbz : boundary R n z = 0 := by
    rw [hz, map_sub, map_sub, ← LinearMap.comp_apply (boundary R n) (φ (n + 1)), hφd,
      ← LinearMap.comp_apply (boundary R n) (ψ (n + 1)), hψd, LinearMap.comp_apply,
      LinearMap.comp_apply, hprev, sub_self]
  rw [carrierHomotopy_succ_single, ← hz, map_smul, boundary_cone_succ hzP, hbz, map_zero,
    zero_add, smul_smul, ← pow_add, Even.neg_one_pow ⟨n + 1, by ring⟩, one_smul, hz,
    sub_add_cancel]

include hcone hinsert hmono hφ hψ hε hφd hψd in
/-- **The homotopy identity in positive degrees**: if `φ` and `ψ` are chain maps agreeing after
augmentation, then `∂ D + D ∂ = φ - ψ` on `(n + 1)`-chains. -/
theorem boundary_comp_carrierHomotopy_succ (n : ℕ) :
    boundary R (n + 1) ∘ₗ carrierHomotopy R φ ψ v (n + 1) +
        carrierHomotopy R φ ψ v n ∘ₗ boundary R n = φ (n + 1) - ψ (n + 1) := by
  induction n with
  | zero =>
    refine boundary_comp_carrierHomotopy_succ_of_boundary hcone hinsert hmono hφ hψ (hφd 0)
      (hψd 0) fun y ↦ ?_
    rw [← LinearMap.comp_apply (boundary R 0),
      boundary_comp_carrierHomotopy_zero hcone hφ hψ hε, LinearMap.sub_apply]
  | succ n ih =>
    refine boundary_comp_carrierHomotopy_succ_of_boundary hcone hinsert hmono hφ hψ (hφd _)
      (hψd _) fun y ↦ ?_
    have h := congrArg (fun f ↦ f (boundary R (n + 1) y)) ih
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.sub_apply] at h
    rwa [← LinearMap.comp_apply (boundary R n) (boundary R (n + 1)), boundary_boundary,
      LinearMap.zero_apply, map_zero, add_zero] at h

end Identities

end OrderedSimplicialChain

open OrderedSimplicialChain

section Homotopy

universe u v

variable {α ι : Type u} [LinearOrder α] [LinearOrder ι]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex ι} {R : Type v} [Ring R]

variable {φ ψ : ∀ n, OrderedSimplicialChain K R n →ₗ[R] OrderedSimplicialChain L R n}
  (hφd : ∀ n, boundary R n ∘ₗ φ (n + 1) = φ n ∘ₗ boundary R n)
  (hψd : ∀ n, boundary R n ∘ₗ ψ (n + 1) = ψ n ∘ₗ boundary R n)
  {v : TauCeti.SetLike.Face K → ι} {P : TauCeti.SetLike.Face K → Finset ι → Prop}
  (hcone : ∀ σ, ∀ s ∈ L, P σ s → (∀ w ∈ s, w ≤ v σ) ∧ insert (v σ) s ∈ L)
  (hinsert : ∀ σ, ∀ s ∈ L, P σ s → P σ (insert (v σ) s))
  (hmono : ∀ ⦃τ σ : TauCeti.SetLike.Face K⦄, τ ≤ σ → ∀ s ∈ L, P τ s → P σ s)
  (hφ : ∀ n (c : RealizationCell K n), ∀ d ∈ (φ n (single c 1)).support, P c.val d.val.val)
  (hψ : ∀ n (c : RealizationCell K n), ∀ d ∈ (ψ n (single c 1)).support, P c.val d.val.val)
  (hε : linearCombination R (fun _ : RealizationCell L 0 ↦ (1 : R)) ∘ₗ φ 0 =
      linearCombination R (fun _ : RealizationCell L 0 ↦ (1 : R)) ∘ₗ ψ 0)

/-- **The acyclic carrier theorem for cone carriers.** Two chain maps of ordered chain complexes,
given by linear maps `φ` and `ψ` of ordered chains that agree after augmentation, are chain
homotopic as soon as they have a common cone carrier: a vertex `v σ` of `L` and a collection
`P σ` of faces of `L` for each face `σ` of `K`, such that `P σ` lies in the closed cone at
`v σ`, is closed under adjoining `v σ` and increases with `σ`, and supports `φ σ` and `ψ σ`. The
homotopy is the operator `carrierHomotopy`. -/
def orderedSimplicialChainComplexHomotopyOfCarrier :
    Homotopy (orderedSimplicialChainComplexHomOfLinear R φ hφd)
      (orderedSimplicialChainComplexHomOfLinear R ψ hψd) :=
  Homotopy.equivSubZero.symm <| Homotopy.mkChainComplex _
    (fun n ↦ orderedSimplicialChainComplexHomOfLinearMap R (carrierHomotopy R φ ψ v n))
    (by
      rw [HomologicalComplex.sub_f_apply, orderedSimplicialChainComplexHomOfLinear_f,
        orderedSimplicialChainComplexHomOfLinear_f,
        orderedSimplicialChainComplex_d_eq_homOfLinearMap,
        orderedSimplicialChainComplexHomOfLinearMap_sub,
        orderedSimplicialChainComplexHomOfLinearMap_comp,
        boundary_comp_carrierHomotopy_zero hcone hφ hψ hε])
    fun n ↦ by
      rw [HomologicalComplex.sub_f_apply, orderedSimplicialChainComplexHomOfLinear_f,
        orderedSimplicialChainComplexHomOfLinear_f,
        orderedSimplicialChainComplex_d_eq_homOfLinearMap,
        orderedSimplicialChainComplex_d_eq_homOfLinearMap,
        orderedSimplicialChainComplexHomOfLinearMap_sub,
        orderedSimplicialChainComplexHomOfLinearMap_comp,
        orderedSimplicialChainComplexHomOfLinearMap_comp,
        orderedSimplicialChainComplexHomOfLinearMap_add]
      exact congrArg (orderedSimplicialChainComplexHomOfLinearMap R)
        ((boundary_comp_carrierHomotopy_succ hcone hinsert hmono hφ hψ hε hφd hψd n).symm.trans
          (add_comm _ _))

/-- The components of the chain homotopy of a cone carrier are the homotopy operator. -/
@[simp]
theorem orderedSimplicialChainComplexHomotopyOfCarrier_hom (n : ℕ) :
    (orderedSimplicialChainComplexHomotopyOfCarrier hφd hψd hcone hinsert hmono hφ hψ hε).hom n
      (n + 1) = orderedSimplicialChainComplexHomOfLinearMap R (carrierHomotopy R φ ψ v n) := by
  simp [orderedSimplicialChainComplexHomotopyOfCarrier, Homotopy.equivSubZero]

end Homotopy

end TauCeti
