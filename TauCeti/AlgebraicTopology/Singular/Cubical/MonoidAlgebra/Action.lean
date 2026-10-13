/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.DGAlgebra
public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Constructions

/-!
# Cubical chains on a space with a right action of a topological monoid

Let `G` be a topological monoid acting continuously and strictly on a space `Y` from the right,
written `y · g = op g • y`.  The action `Y × G → Y` and the cross product of normalized cubical
chains give a right action of the Pontryagin algebra on the chains of `Y`:
`c · a := act_* (c × a) : C^□_{p + q}(Y; R)` for `c ∈ C^□_p(Y; R)` and `a ∈ C^□_q(G; R)`.  It is
strictly associative and unital, and the boundary is a derivation for it with the Koszul sign.
Hence `⨁ n, C^□_n(Y; R)`, with `C^□_n` in cohomological degree `-n`, is a **differential graded
right module** over the DG algebra `⨁ n, C^□_n(G; R)` of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.DGAlgebra`.

An equivariant continuous map `Y → Y'` induces a morphism of these DG right modules, functorially.

The module `TauCeti.cubicalChainModule Y G R` is a one-field wrapper around
`normalizedCubicalChainAlgebra Y R`, linearly equivalent to it
(`TauCeti.cubicalChainModuleEquiv`): for `Y = G` acting on itself by right multiplication, the
algebra already acts on itself, and the wrapper keeps the two actions apart.

## Main definitions

* `TauCeti.actMap Y G`: the action `Y × G → Y`, `(y, g) ↦ op g • y`.
* `TauCeti.NormalizedCubicalChain.act Y G R p q`: the action
  `C^□_p(Y; R) ⊗ C^□_q(G; R) → C^□_{p + q}(Y; R)`.
* `TauCeti.cubicalChainModule Y G R`: the DG right module `⨁ n, C^□_n(Y; R)`.
* `TauCeti.cubicalChainModuleDG Y G R`: it, as an object of `DGRightModuleCat`.
* `TauCeti.cubicalChainModuleMap R f hf`: the morphism induced by an equivariant map.

## Main results

* `TauCeti.NormalizedCubicalChain.act_assoc`, `TauCeti.NormalizedCubicalChain.act_one`: the
  action is strictly associative and unital.
* `TauCeti.NormalizedCubicalChain.boundary_act`: the Leibniz rule.
* `TauCeti.cubicalChainModule_isDGRightModule`: the chains form a DG right module.
* `TauCeti.cubicalChainModuleMap_id`, `TauCeti.cubicalChainModuleMap_comp`: functoriality.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public section

noncomputable section

open MulOpposite DirectSum

namespace TauCeti

section ActMap

variable (Y G : Type*) [TopologicalSpace Y] [TopologicalSpace G] [SMul Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y]

/-- The right action of `G` on `Y` as a continuous map `Y × G → Y`, `(y, g) ↦ op g • y`. -/
def actMap : C(Y × G, Y) :=
  ⟨fun x ↦ op x.2 • x.1, (continuous_op.comp continuous_snd).smul continuous_fst⟩

@[simp]
theorem actMap_apply (x : Y × G) : actMap Y G x = op x.2 • x.1 :=
  (rfl)

end ActMap

namespace NormalizedCubicalChain

section Act

variable (Y G : Type*) [TopologicalSpace Y] [TopologicalSpace G] [SMul Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] (R : Type*) [CommRing R]

/-- The **action of chains on `G` on chains on `Y`**: `c · a = act_* (c × a)`. -/
def act (p q : ℕ) :
    NormalizedCubicalChain Y R p →ₗ[R] NormalizedCubicalChain G R q →ₗ[R]
      NormalizedCubicalChain Y R (p + q) :=
  LinearMap.compr₂ (crossProduct Y G R p q) (map R (actMap Y G) (p + q))

variable {Y G R}

/-- The action is the push-forward of the cross product along the action map. -/
theorem act_def {p q : ℕ} (c : NormalizedCubicalChain Y R p) (a : NormalizedCubicalChain G R q) :
    act Y G R p q c a = map R (actMap Y G) (p + q) (crossProduct Y G R p q c a) :=
  (rfl)

/-- **The Leibniz rule for the action**: for `c` of degree `p + 1` and `a` of degree `q + 1`,
`∂ (c · a) = ∂ c · a + (-1) ^ (p + 1) • (c · ∂ a)`, in degree `p + q + 1`. -/
theorem boundary_act {p q : ℕ} (c : NormalizedCubicalChain Y R (p + 1))
    (a : NormalizedCubicalChain G R (q + 1)) :
    boundary Y R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1) (act Y G R (p + 1) (q + 1) c a)) =
      act Y G R p (q + 1) (boundary Y R p c) a +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (act Y G R (p + 1) q c (boundary G R q a)) := by
  simp only [act_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary Y R _), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct, map_add, map_smul, map_cast]
  rfl

/-- The Leibniz rule for the action of a `0`-chain. -/
theorem boundary_act_zero_right {p : ℕ} (c : NormalizedCubicalChain Y R (p + 1))
    (a : NormalizedCubicalChain G R 0) :
    boundary Y R p (act Y G R (p + 1) 0 c a) = act Y G R p 0 (boundary Y R p c) a := by
  simp only [act_def]
  rw [← LinearMap.comp_apply (boundary Y R p), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_right]
  rfl

/-- The Leibniz rule for the action on a `0`-chain. -/
theorem boundary_act_zero_left {q : ℕ} (c : NormalizedCubicalChain Y R 0)
    (a : NormalizedCubicalChain G R (q + 1)) :
    boundary Y R q (cast R (Nat.zero_add (q + 1)) (act Y G R 0 (q + 1) c a)) =
      cast R (Nat.zero_add q) (act Y G R 0 q c (boundary G R q a)) := by
  simp only [act_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary Y R q), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_left, map_cast]

variable {Y' : Type*} [TopologicalSpace Y'] [SMul Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y']

/-- Pushing forward along an equivariant map commutes with the action. -/
theorem map_act (f : C(Y, Y')) (hf : ∀ (g : G) (y : Y), f (op g • y) = op g • f y) {p q : ℕ}
    (c : NormalizedCubicalChain Y R p) (a : NormalizedCubicalChain G R q) :
    map R f (p + q) (act Y G R p q c a) = act Y' G R p q (map R f p c) a := by
  have key : f.comp (actMap Y G) = (actMap Y' G).comp (f.prodMap (ContinuousMap.id G)) := by
    ext x
    simp [hf]
  rw [act_def, act_def, ← LinearMap.comp_apply (map R f (p + q)), ← map_comp, key, map_comp,
    LinearMap.comp_apply, map_crossProduct, map_id, LinearMap.id_apply]

end Act

section MulAction

variable {Y G : Type*} [TopologicalSpace Y] [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] {R : Type*} [CommRing R]

/-- **Strict associativity of the action**, after the reindexing `(p + q) + r = p + (q + r)`:
`(c · a) · b = c · (a b)`. -/
theorem act_assoc {p q r : ℕ} (c : NormalizedCubicalChain Y R p) (a : NormalizedCubicalChain G R q)
    (b : NormalizedCubicalChain G R r) :
    cast R (Nat.add_assoc p q r) (act Y G R (p + q) r (act Y G R p q c a) b) =
      act Y G R p (q + r) c (mul G R q r a b) := by
  simp only [act_def, mul_def]
  refine map_crossProduct_map_assoc R ?_ c a b
  ext x
  simp [Homeomorph.prodAssoc, Equiv.prodAssoc, mul_smul]

omit [ContinuousMul G] in
/-- **The unit acts trivially**, after the reindexing `p + 0 = p`. -/
theorem act_one {p : ℕ} (c : NormalizedCubicalChain Y R p) :
    cast R (Nat.add_zero p) (act Y G R p 0 c (one G R)) = c := by
  have h : (actMap Y G).comp
      (ContinuousMap.prodMk (ContinuousMap.id Y) (ContinuousMap.const Y (1 : G))) =
        ContinuousMap.id Y := by
    ext x
    simp
  rw [act_def, one_def, ← map_cast, crossProduct_point_right, ← LinearMap.comp_apply, ← map_comp,
    h, map_id, LinearMap.id_apply]

omit [ContinuousMul G] in
/-- The unit law in simp normal form: since `p + 0` reduces to `p`, no reindexing is needed. -/
@[simp]
theorem act_one_eq_self {p : ℕ} (c : NormalizedCubicalChain Y R p) :
    act Y G R p 0 c (one G R) = c := by
  simpa using act_one c

end MulAction

end NormalizedCubicalChain

open NormalizedCubicalChain

section Carrier

/-- The **DG right module of cubical chains** of a space `Y` with a right action of `G`: the direct
sum `⨁ n, C^□_n(Y; R)`, acted on by the chains of `G`.  It is a one-field wrapper around
`normalizedCubicalChainAlgebra Y R` rather than that type itself: for `Y = G` acting on itself the
algebra already acts on itself, and the wrapper keeps the two actions apart.  The monoid `G` is a
phantom parameter, recording which action is meant. -/
structure cubicalChainModule (Y : Type*) [TopologicalSpace Y] (_G : Type*) (R : Type*)
    [CommRing R] where
  /-- The element of the module given by a chain of the direct sum. -/
  ofSum ::
  /-- The underlying chain of the direct sum. -/
  toSum : normalizedCubicalChainAlgebra Y R

variable (Y G : Type*) [TopologicalSpace Y] (R : Type*) [CommRing R]

/-- The additive group structure, transported from the direct sum. -/
instance : AddCommGroup (cubicalChainModule Y G R) :=
  fast_instance% (⟨cubicalChainModule.toSum, cubicalChainModule.ofSum, fun _ ↦ rfl, fun _ ↦ rfl⟩ :
    cubicalChainModule Y G R ≃ normalizedCubicalChainAlgebra Y R).addCommGroup

/-- The `R`-module structure, transported from the direct sum. -/
instance : Module R (cubicalChainModule Y G R) :=
  (⟨⟨cubicalChainModule.toSum, cubicalChainModule.ofSum, fun _ ↦ rfl, fun _ ↦ rfl⟩,
    fun _ _ ↦ rfl⟩ : cubicalChainModule Y G R ≃+ normalizedCubicalChainAlgebra Y R).module R

/-- The module is linearly equivalent to the direct sum of the normalized cubical chains. -/
def cubicalChainModuleEquiv : cubicalChainModule Y G R ≃ₗ[R] normalizedCubicalChainAlgebra Y R where
  toFun := cubicalChainModule.toSum
  invFun := cubicalChainModule.ofSum
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inclusion of the chains of dimension `n` into the module. -/
def cubicalChainModuleLof (n : ℕ) :
    NormalizedCubicalChain Y R n →ₗ[R] cubicalChainModule Y G R :=
  (cubicalChainModuleEquiv Y G R).symm.toLinearMap ∘ₗ cubicalChainLof Y R n

/-- The grading of the module, with `C^□_n` in cohomological degree `-n`. -/
def cubicalChainModuleGrading (i : ℤ) : Submodule R (cubicalChainModule Y G R) :=
  (cubicalChainGrading Y R i).comap (cubicalChainModuleEquiv Y G R).toLinearMap

/-- The differential of the module: the boundary. -/
def cubicalChainModuleDifferential : cubicalChainModule Y G R →ₗ[R] cubicalChainModule Y G R :=
  (cubicalChainModuleEquiv Y G R).symm.toLinearMap ∘ₗ cubicalChainDifferential Y R ∘ₗ
    (cubicalChainModuleEquiv Y G R).toLinearMap

variable {Y G R}

/-- The linear map out of the module given by linear maps out of its homogeneous parts. -/
def cubicalChainModuleDesc {N : Type*} [AddCommMonoid N] [Module R N]
    (φ : ∀ n, NormalizedCubicalChain Y R n →ₗ[R] N) : cubicalChainModule Y G R →ₗ[R] N :=
  DirectSum.toModule R ℕ N φ ∘ₗ (cubicalChainModuleEquiv Y G R).toLinearMap

/-- The equivalence with the direct sum sends a homogeneous chain to itself. -/
@[simp]
theorem cubicalChainModuleEquiv_lof {n : ℕ} (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleEquiv Y G R (cubicalChainModuleLof Y G R n c) = cubicalChainLof Y R n c :=
  (rfl)

/-- Reindexing a chain does not change its image in the module. -/
theorem cubicalChainModuleLof_cast {n m : ℕ} (h : n = m) (x : NormalizedCubicalChain Y R n) :
    cubicalChainModuleLof Y G R m (cast R h x) = cubicalChainModuleLof Y G R n x := by
  rw [cubicalChainModuleLof, LinearMap.comp_apply, cubicalChainLof_cast]
  rfl

/-- Induction on the module: a property holds for every element once it holds for `0`, for the
homogeneous chains and is closed under sums. -/
@[elab_as_elim]
theorem cubicalChainModule.induction_on {motive : cubicalChainModule Y G R → Prop}
    (m : cubicalChainModule Y G R) (zero : motive 0)
    (lof : ∀ (n : ℕ) (c : NormalizedCubicalChain Y R n), motive (cubicalChainModuleLof Y G R n c))
    (add : ∀ m m', motive m → motive m' → motive (m + m')) : motive m := by
  obtain ⟨s⟩ := m
  induction s using DirectSum.induction_on with
  | zero => exact zero
  | of n c => exact lof n c
  | add a b ha hb => exact add _ _ ha hb

/-- The linear map given by homogeneous parts, on a homogeneous chain. -/
@[simp]
theorem cubicalChainModuleDesc_lof {N : Type*} [AddCommMonoid N] [Module R N]
    (φ : ∀ n, NormalizedCubicalChain Y R n →ₗ[R] N) {n : ℕ} (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleDesc (G := G) φ (cubicalChainModuleLof Y G R n c) = φ n c :=
  DirectSum.toModule_lof R n c

/-- Two linear maps out of the module agree when they agree on homogeneous chains. -/
theorem cubicalChainModule_linearMap_ext {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : cubicalChainModule Y G R →ₗ[R] N}
    (h : ∀ (n : ℕ) (c : NormalizedCubicalChain Y R n),
      f (cubicalChainModuleLof Y G R n c) = g (cubicalChainModuleLof Y G R n c)) : f = g :=
  LinearMap.ext fun m ↦ by
    induction m using cubicalChainModule.induction_on with
    | zero => rw [map_zero, map_zero]
    | lof n c => exact h n c
    | add m m' hm hm' => rw [map_add, map_add, hm, hm']

/-- Membership in a graded piece of the module: zero, or a chain of dimension `-i`. -/
theorem mem_cubicalChainModuleGrading_iff {i : ℤ} {m : cubicalChainModule Y G R} :
    m ∈ cubicalChainModuleGrading Y G R i ↔
      m = 0 ∨ ∃ (n : ℕ) (c : NormalizedCubicalChain Y R n), (n : ℤ) = -i ∧
        cubicalChainModuleLof Y G R n c = m := by
  rw [cubicalChainModuleGrading, Submodule.mem_comap, LinearEquiv.coe_coe,
    mem_cubicalChainGrading_iff, ← (cubicalChainModuleEquiv Y G R).map_eq_zero_iff]
  refine or_congr Iff.rfl (exists_congr fun n ↦ exists_congr fun c ↦ and_congr Iff.rfl ?_)
  rw [← cubicalChainModuleEquiv_lof (G := G), (cubicalChainModuleEquiv Y G R).injective.eq_iff]

/-- Membership in a graded piece of the module is membership of the underlying chain of the direct
sum. -/
theorem mem_cubicalChainModuleGrading {i : ℤ} {m : cubicalChainModule Y G R} :
    m ∈ cubicalChainModuleGrading Y G R i ↔
      cubicalChainModuleEquiv Y G R m ∈ cubicalChainGrading Y R i :=
  Iff.rfl

/-- A chain of dimension `n` lies in cohomological degree `-n`. -/
theorem cubicalChainModuleLof_mem {n : ℕ} (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleLof Y G R n c ∈ cubicalChainModuleGrading Y G R (-(n : ℤ)) :=
  mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨n, c, by simp, rfl⟩)

variable (Y G R) in
/-- The decomposition of the module along its grading. -/
def cubicalChainModuleDecompose :
    cubicalChainModule Y G R →ₗ[R] ⨁ i : ℤ, cubicalChainModuleGrading Y G R i :=
  cubicalChainModuleDesc (G := G) fun n ↦
    (DirectSum.lof R ℤ (fun i ↦ cubicalChainModuleGrading Y G R i) (-(n : ℤ))).comp
      ((cubicalChainModuleLof Y G R n).codRestrict _ cubicalChainModuleLof_mem)

/-- The module is the internal direct sum of its graded pieces: an element decomposes into its
homogeneous chains, the chains of dimension `n` lying in cohomological degree `-n`. -/
instance : DirectSum.Decomposition (cubicalChainModuleGrading Y G R) :=
  DirectSum.Decomposition.ofLinearMap _ (cubicalChainModuleDecompose Y G R)
    (cubicalChainModule_linearMap_ext fun n c ↦ by
      simp [cubicalChainModuleDecompose])
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      obtain ⟨x, hx⟩ := x
      rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
      · simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, map_zero,
          LinearMap.id_apply]
        exact (map_zero (DirectSum.lof R ℤ (fun i ↦ cubicalChainModuleGrading Y G R i) i)).symm
      · obtain rfl : i = -(n : ℤ) := by omega
        simp [cubicalChainModuleDecompose]
        rfl)

/-- The differential vanishes on `0`-chains. -/
@[simp]
theorem cubicalChainModuleDifferential_lof_zero (c : NormalizedCubicalChain Y R 0) :
    cubicalChainModuleDifferential Y G R (cubicalChainModuleLof Y G R 0 c) = 0 := by
  simp [cubicalChainModuleDifferential]

/-- The differential on `(k + 1)`-chains is the boundary. -/
@[simp]
theorem cubicalChainModuleDifferential_lof_succ (k : ℕ) (c : NormalizedCubicalChain Y R (k + 1)) :
    cubicalChainModuleDifferential Y G R (cubicalChainModuleLof Y G R (k + 1) c) =
      cubicalChainModuleLof Y G R k (boundary Y R k c) := by
  simp [cubicalChainModuleDifferential, cubicalChainModuleLof]

/-- The differential of the module is the boundary, read through the equivalence with the direct
sum. -/
theorem cubicalChainModuleEquiv_differential (m : cubicalChainModule Y G R) :
    cubicalChainModuleEquiv Y G R (cubicalChainModuleDifferential Y G R m) =
      cubicalChainDifferential Y R (cubicalChainModuleEquiv Y G R m) := by
  simp [cubicalChainModuleDifferential]

variable (Y G R) in
/-- The differential of the module raises the cohomological degree by one. -/
theorem cubicalChainModuleDifferential_isHomogeneous :
    LinearMap.IsHomogeneous (cubicalChainModuleDifferential Y G R) (cubicalChainModuleGrading Y G R)
      (cubicalChainModuleGrading Y G R) 1 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
    rw [mem_cubicalChainModuleGrading, cubicalChainModuleEquiv_differential]
    exact cubicalChainDifferential_mem Y R (mem_cubicalChainModuleGrading.1 hx)

/-- The differential of the module squares to zero. -/
@[simp]
theorem cubicalChainModuleDifferential_cubicalChainModuleDifferential
    (m : cubicalChainModule Y G R) :
    cubicalChainModuleDifferential Y G R (cubicalChainModuleDifferential Y G R m) = 0 :=
  (cubicalChainModuleEquiv Y G R).injective (by
    rw [cubicalChainModuleEquiv_differential, cubicalChainModuleEquiv_differential,
      cubicalChainDifferential_cubicalChainDifferential, map_zero])

/-- The sign `(-1) ^ (-n)` acts on the module as `(-1) ^ n ∈ R`. -/
theorem negOnePow_neg_natCast_smul_cubicalChainModule (n : ℕ) (m : cubicalChainModule Y G R) :
    (-(n : ℤ)).negOnePow • m = (-1 : R) ^ n • m :=
  (cubicalChainModuleEquiv Y G R).injective (by
    rw [map_zsmul_unit, map_smul]
    exact negOnePow_neg_natCast_smul Y R n _)

end Carrier

section Action

variable (Y G : Type*) [TopologicalSpace Y] [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] (R : Type*) [CommRing R]

/-- The action of a homogeneous chain of `G` on a homogeneous chain of `Y`, landing in the
module. -/
def cubicalChainActLof (p q : ℕ) :
    NormalizedCubicalChain Y R p →ₗ[R] NormalizedCubicalChain G R q →ₗ[R]
      cubicalChainModule Y G R :=
  (act Y G R p q).compr₂ (cubicalChainModuleLof Y G R (p + q))

/-- The action as a bilinear map `M × A → M`, `(m, a) ↦ m · a`. -/
def cubicalChainActBilin :
    cubicalChainModule Y G R →ₗ[R] normalizedCubicalChainAlgebra G R →ₗ[R]
      cubicalChainModule Y G R :=
  cubicalChainModuleDesc fun p ↦
    (DirectSum.toModule R ℕ (NormalizedCubicalChain Y R p →ₗ[R] cubicalChainModule Y G R)
      fun q ↦ (cubicalChainActLof Y G R p q).flip).flip

variable {Y G R}

omit [ContinuousMul G] in
/-- The action on homogeneous elements. -/
@[simp]
theorem cubicalChainActBilin_lof_lof {p q : ℕ} (c : NormalizedCubicalChain Y R p)
    (a : NormalizedCubicalChain G R q) :
    cubicalChainActBilin Y G R (cubicalChainModuleLof Y G R p c) (cubicalChainLof G R q a) =
      cubicalChainModuleLof Y G R (p + q) (act Y G R p q c a) := by
  rw [cubicalChainActBilin, cubicalChainModuleDesc_lof, LinearMap.flip_apply,
    DirectSum.toModule_lof]
  rfl

omit [ContinuousMul G] in
/-- The unit acts trivially on the module. -/
theorem cubicalChainActBilin_one (m : cubicalChainModule Y G R) :
    cubicalChainActBilin Y G R m 1 = m := by
  have h1 : (1 : normalizedCubicalChainAlgebra G R) = cubicalChainLof G R 0 (one G R) := by
    rw [DirectSum.lof_eq_of]
    rfl
  rw [h1]
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | lof n c =>
    rw [cubicalChainActBilin_lof_lof, act_one_eq_self]
    rfl
  | add m m' hm hm' => rw [map_add, LinearMap.add_apply, hm, hm']

/-- The action is associative: `m · (a b) = (m · a) · b`. -/
theorem cubicalChainActBilin_mul (m : cubicalChainModule Y G R)
    (a b : normalizedCubicalChainAlgebra G R) :
    cubicalChainActBilin Y G R m (a * b) =
      cubicalChainActBilin Y G R (cubicalChainActBilin Y G R m a) b := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | lof p c =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, LinearMap.add_apply, ha, ha']
    | of q x =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
      | of r y =>
        rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, cubicalChainLof_mul,
          cubicalChainActBilin_lof_lof, cubicalChainActBilin_lof_lof,
          cubicalChainActBilin_lof_lof, ← act_assoc, cubicalChainModuleLof_cast]

variable (Y G R)

/-- The action of the chain algebra of `G` on the module, as a ring homomorphism from the opposite
algebra to the endomorphisms. -/
def cubicalChainActHom :
    (normalizedCubicalChainAlgebra G R)ᵐᵒᵖ →+* Module.End R (cubicalChainModule Y G R) where
  toFun a := (cubicalChainActBilin Y G R).flip a.unop
  map_one' := LinearMap.ext fun m ↦ cubicalChainActBilin_one m
  map_mul' a b := LinearMap.ext fun m ↦ cubicalChainActBilin_mul m b.unop a.unop
  map_zero' := by simp
  map_add' a b := by simp

/-- The chains of `Y` form a right module over the chains of `G`. -/
instance : Module (normalizedCubicalChainAlgebra G R)ᵐᵒᵖ (cubicalChainModule Y G R) :=
  Module.compHom _ (cubicalChainActHom Y G R)

variable {Y G R}

/-- The right action of a chain of `G`. -/
theorem op_smul_cubicalChainModule (a : normalizedCubicalChainAlgebra G R)
    (m : cubicalChainModule Y G R) : op a • m = cubicalChainActBilin Y G R m a :=
  (rfl)

/-- The right action of a homogeneous chain of `G` on a homogeneous chain of `Y`. -/
@[simp]
theorem op_lof_smul_cubicalChainModuleLof {p q : ℕ} (c : NormalizedCubicalChain Y R p)
    (a : NormalizedCubicalChain G R q) :
    op (cubicalChainLof G R q a) • cubicalChainModuleLof Y G R p c =
      cubicalChainModuleLof Y G R (p + q) (act Y G R p q c a) :=
  cubicalChainActBilin_lof_lof c a

/-- The ground ring and the chains of `G` act compatibly: `(r • a)` acts as `r` times the action of
`a`, since the action is bilinear. -/
instance : IsScalarTower R (normalizedCubicalChainAlgebra G R)ᵐᵒᵖ (cubicalChainModule Y G R) where
  smul_assoc r a m := by
    rw [← op_unop a, ← MulOpposite.op_smul, op_smul_cubicalChainModule,
      op_smul_cubicalChainModule, map_smul]

/-- The action is graded: a chain of `G` of cohomological degree `i` sends the chains of `Y` of
degree `j` to degree `i + j`, as the action adds dimensions. -/
instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading G R)).opposite.piece
    (cubicalChainModuleGrading Y G R) where
  smul_mem := by
    intro i j a m ha hm
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
    rw [← op_unop a, vadd_eq_add]
    rcases (mem_cubicalChainGrading_iff G R).1 ha with h | ⟨q, x, hq, hx⟩
    · rw [h, op_zero, zero_smul]
      exact zero_mem _
    rcases mem_cubicalChainModuleGrading_iff.1 hm with rfl | ⟨p, c, hp, rfl⟩
    · rw [smul_zero]
      exact zero_mem _
    rw [← hx, op_lof_smul_cubicalChainModuleLof]
    exact mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨p + q, _, by push_cast; omega, rfl⟩)

/-- The graded Leibniz rule for the action on homogeneous chains. -/
theorem cubicalChainModuleDifferential_act {m q : ℕ} (c : NormalizedCubicalChain Y R m)
    (a : NormalizedCubicalChain G R q) :
    cubicalChainModuleDifferential Y G R
        (op (cubicalChainLof G R q a) • cubicalChainModuleLof Y G R m c) =
      op (cubicalChainLof G R q a) •
          cubicalChainModuleDifferential Y G R (cubicalChainModuleLof Y G R m c) +
        (-(m : ℤ)).negOnePow • (op (cubicalChainDifferential G R (cubicalChainLof G R q a)) •
          cubicalChainModuleLof Y G R m c) := by
  rw [op_lof_smul_cubicalChainModuleLof, negOnePow_neg_natCast_smul_cubicalChainModule]
  have h0 : ∀ n : ℕ, ((-1 : R) ^ n) • (0 : cubicalChainModule Y G R) = 0 :=
    fun n ↦ smul_zero (M := R) (A := cubicalChainModule Y G R) _
  rcases m with _ | k <;> rcases q with _ | j
  · rw [cubicalChainModuleDifferential_lof_zero, cubicalChainModuleDifferential_lof_zero,
      cubicalChainDifferential_lof_zero, smul_zero, op_zero, zero_smul, h0, zero_add]
  · have hL : cubicalChainModuleDifferential Y G R
        (cubicalChainModuleLof Y G R (0 + (j + 1)) (act Y G R 0 (j + 1) c a)) =
          cubicalChainModuleLof Y G R (0 + j) (act Y G R 0 j c (boundary G R j a)) := by
      refine (cubicalChainModuleDifferential_lof_succ (0 + j) (act Y G R 0 (j + 1) c a)).trans ?_
      congr 1
      apply cast_injective R (Nat.zero_add j)
      exact (boundary_cast R (Nat.zero_add j) (act Y G R 0 (j + 1) c a)).symm.trans
        (boundary_act_zero_left c a)
    rw [hL, cubicalChainModuleDifferential_lof_zero, cubicalChainDifferential_lof_succ,
      op_lof_smul_cubicalChainModuleLof, smul_zero, zero_add (M := cubicalChainModule Y G R),
      pow_zero, one_smul]
  · refine (cubicalChainModuleDifferential_lof_succ k (act Y G R (k + 1) 0 c a)).trans ?_
    rw [boundary_act_zero_right, cubicalChainModuleDifferential_lof_succ,
      cubicalChainDifferential_lof_zero, op_zero, zero_smul, op_lof_smul_cubicalChainModuleLof,
      h0, add_zero (M := cubicalChainModule Y G R)]
    rfl
  · refine (cubicalChainModuleDifferential_lof_succ (k + 1 + j)
      (act Y G R (k + 1) (j + 1) c a)).trans ?_
    have h' : k + 1 + j = k + j + 1 := by omega
    have e : cast R h' (boundary Y R (k + 1 + j) (act Y G R (k + 1) (j + 1) c a)) =
        act Y G R k (j + 1) (boundary Y R k c) a +
          (-1 : R) ^ (k + 1) • cast R h' (act Y G R (k + 1) j c (boundary G R j a)) :=
      (boundary_cast R h' (act Y G R (k + 1) (j + 1) c a)).symm.trans (boundary_act c a)
    rw [cubicalChainModuleDifferential_lof_succ, cubicalChainDifferential_lof_succ,
      op_lof_smul_cubicalChainModuleLof, op_lof_smul_cubicalChainModuleLof,
      ← cubicalChainModuleLof_cast h', e, map_add, map_smul, cubicalChainModuleLof_cast]
    rfl

variable (Y G R)

/-- **The cubical chains of a space with a right action of a topological monoid `G` form a
differential graded right module** over the DG algebra of cubical chains of `G`. -/
theorem cubicalChainModule_isDGRightModule :
    IsDGRightModule (cubicalChain_isDGAlgebra G R) (cubicalChainModuleGrading Y G R)
      (cubicalChainModuleDifferential Y G R) where
  isHomogeneous := cubicalChainModuleDifferential_isHomogeneous Y G R
  sq_zero := cubicalChainModuleDifferential_cubicalChainModuleDifferential
  leibniz := fun {q} {x} hx a ↦ by
    rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨m, c, hm, rfl⟩
    · simp
    obtain rfl : q = -(m : ℤ) := by omega
    induction a using DirectSum.induction_on with
    | zero => simp
    | of r z =>
      rw [← DirectSum.lof_eq_of R]
      exact cubicalChainModuleDifferential_act c z
    | add a a' ha ha' =>
      rw [map_add, op_add, add_smul, map_add, ha, ha', op_add, add_smul, add_smul, smul_add]
      abel

/-- The cubical chains of `Y` as an object of the category of DG right modules over the chains of
`G`. -/
abbrev cubicalChainModuleDG : DGRightModuleCat (cubicalChain_isDGAlgebra G R) :=
  DGRightModuleCat.of (cubicalChainModule_isDGRightModule Y G R)

end Action

section Map

open CategoryTheory

universe u

variable {Y Y' Y'' : Type u} {G : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Y'']
  [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y']
  [MulAction Gᵐᵒᵖ Y''] [ContinuousSMul Gᵐᵒᵖ Y''] (R : Type*) [CommRing R]

/-- The `R`-linear map of modules induced by a continuous map: the push-forward of chains in each
dimension. -/
def cubicalChainModuleLinearMap (f : C(Y, Y')) :
    cubicalChainModule Y G R →ₗ[R] cubicalChainModule Y' G R :=
  cubicalChainModuleDesc fun n ↦ (cubicalChainModuleLof Y' G R n).comp (map R f n)

variable {R}

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The induced map on a homogeneous chain. -/
@[simp]
theorem cubicalChainModuleLinearMap_lof (f : C(Y, Y')) {n : ℕ} (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleLinearMap (G := G) R f (cubicalChainModuleLof Y G R n c) =
      cubicalChainModuleLof Y' G R n (map R f n c) :=
  cubicalChainModuleDesc_lof _ c

/-- The induced map of an equivariant map commutes with the action. -/
theorem cubicalChainModuleLinearMap_op_smul (f : C(Y, Y'))
    (hf : ∀ (g : G) (y : Y), f (op g • y) = op g • f y) (a : normalizedCubicalChainAlgebra G R)
    (x : cubicalChainModule Y G R) :
    cubicalChainModuleLinearMap R f (op a • x) = op a • cubicalChainModuleLinearMap R f x := by
  induction x using cubicalChainModule.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | lof p c =>
    induction a using DirectSum.induction_on with
    | zero => rw [op_zero, zero_smul, map_zero, zero_smul]
    | add a a' ha ha' => rw [op_add, add_smul, map_add, ha, ha', add_smul]
    | of q z =>
      rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof,
        cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof,
        op_lof_smul_cubicalChainModuleLof, map_act f hf]

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The induced map commutes with the differentials. -/
theorem cubicalChainModuleDifferential_linearMap (f : C(Y, Y')) (x : cubicalChainModule Y G R) :
    cubicalChainModuleDifferential Y' G R (cubicalChainModuleLinearMap R f x) =
      cubicalChainModuleLinearMap R f (cubicalChainModuleDifferential Y G R x) := by
  induction x using cubicalChainModule.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | lof n c =>
    rcases n with _ | k
    · rw [cubicalChainModuleLinearMap_lof, cubicalChainModuleDifferential_lof_zero,
        cubicalChainModuleDifferential_lof_zero, map_zero]
    · rw [cubicalChainModuleLinearMap_lof, cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleDifferential_lof_succ, cubicalChainModuleLinearMap_lof,
        ← LinearMap.comp_apply (boundary Y' R k), ← map_boundary, LinearMap.comp_apply]

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The induced map preserves the grading. -/
theorem cubicalChainModuleLinearMap_mem (f : C(Y, Y')) {i : ℤ} {x : cubicalChainModule Y G R}
    (hx : x ∈ cubicalChainModuleGrading Y G R i) :
    cubicalChainModuleLinearMap R f x ∈ cubicalChainModuleGrading Y' G R i := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · rw [map_zero]
    exact zero_mem _
  · exact mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨n, _, hn,
      (cubicalChainModuleLinearMap_lof f c).symm⟩)

variable (R) in
/-- The morphism of DG right modules induced by an equivariant continuous map `f : Y → Y'`. -/
def cubicalChainModuleMap (f : C(Y, Y')) (hf : ∀ (g : G) (y : Y), f (op g • y) = op g • f y) :
    cubicalChainModuleDG Y G R ⟶ cubicalChainModuleDG Y' G R where
  toFun := cubicalChainModuleLinearMap R f
  map_add' := map_add _
  map_smul' a x := by
    rw [← op_unop a]
    exact cubicalChainModuleLinearMap_op_smul f hf a.unop x
  map_mem' := cubicalChainModuleLinearMap_mem f
  map_d' := cubicalChainModuleDifferential_linearMap f

/-- The induced morphism is the push-forward of chains. -/
theorem cubicalChainModuleMap_apply (f : C(Y, Y'))
    (hf : ∀ (g : G) (y : Y), f (op g • y) = op g • f y) (x : cubicalChainModule Y G R) :
    cubicalChainModuleMap R f hf x = cubicalChainModuleLinearMap R f x :=
  (rfl)

/-- The induced morphism on a homogeneous chain. -/
@[simp]
theorem cubicalChainModuleMap_lof (f : C(Y, Y'))
    (hf : ∀ (g : G) (y : Y), f (op g • y) = op g • f y) {n : ℕ} (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleMap R f hf (cubicalChainModuleLof Y G R n c) =
      cubicalChainModuleLof Y' G R n (map R f n c) :=
  cubicalChainModuleLinearMap_lof f c

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] in
/-- The identity map induces the identity. -/
@[simp]
theorem cubicalChainModuleLinearMap_id :
    cubicalChainModuleLinearMap (G := G) R (ContinuousMap.id Y) = LinearMap.id :=
  cubicalChainModule_linearMap_ext fun n c ↦ by
    rw [cubicalChainModuleLinearMap_lof, NormalizedCubicalChain.map_id, LinearMap.id_apply,
      LinearMap.id_apply]

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] [MulAction Gᵐᵒᵖ Y'']
  [ContinuousSMul Gᵐᵒᵖ Y''] in
/-- A composite map induces the composite of the induced maps. -/
theorem cubicalChainModuleLinearMap_comp (f : C(Y, Y')) (g : C(Y', Y'')) :
    cubicalChainModuleLinearMap (G := G) R (g.comp f) =
      cubicalChainModuleLinearMap R g ∘ₗ cubicalChainModuleLinearMap R f :=
  cubicalChainModule_linearMap_ext fun n c ↦ by
    rw [cubicalChainModuleLinearMap_lof, LinearMap.comp_apply, cubicalChainModuleLinearMap_lof,
      cubicalChainModuleLinearMap_lof, NormalizedCubicalChain.map_comp, LinearMap.comp_apply]

/-- The identity map induces the identity morphism. -/
@[simp]
theorem cubicalChainModuleMap_id :
    cubicalChainModuleMap (G := G) R (ContinuousMap.id Y) (fun _ _ ↦ rfl) =
      𝟙 (cubicalChainModuleDG Y G R) := by
  ext x
  rw [DGRightModuleCat.id_apply]
  exact LinearMap.congr_fun (cubicalChainModuleLinearMap_id (G := G) (Y := Y) (R := R)) x

/-- A composite of equivariant maps induces the composite of the induced morphisms. -/
theorem cubicalChainModuleMap_comp (f : C(Y, Y')) (g : C(Y', Y''))
    (hf : ∀ (a : G) (y : Y), f (op a • y) = op a • f y)
    (hg : ∀ (a : G) (y : Y'), g (op a • y) = op a • g y) :
    cubicalChainModuleMap R (g.comp f) (fun a y ↦ by simp [hf, hg]) =
      cubicalChainModuleMap R f hf ≫ cubicalChainModuleMap R g hg := by
  ext x
  rw [DGRightModuleCat.comp_apply]
  exact LinearMap.congr_fun (cubicalChainModuleLinearMap_comp (G := G) (R := R) f g) x

end Map

end TauCeti

end
