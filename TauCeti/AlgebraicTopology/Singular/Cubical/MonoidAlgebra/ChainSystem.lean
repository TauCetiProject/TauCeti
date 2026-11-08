/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Hom
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing
public import TauCeti.Algebra.Homology.DG.Twisted.Map

/-!
# Chain systems on product faces and their twisting cocycles

Let `P` be a finite set graded by `ind : P → ℤ`, and let `M x y` be spaces indexed by pairs of
elements of `P`, with **face maps** `ι x z y : M x z × M z y → M x y`. The basic example is the
family of compactified spaces of connecting trajectories of a Morse function, where `ι x z y`
includes the broken trajectories through `z` into the boundary of `M x y`.

A **product-face chain system** (`TauCeti.ProductFaceChainSystem`) is a family of normalized
cubical chains `s x y` on `M x y`, of dimension `ind x - ind y - 1`, whose boundaries decompose
along the faces:

`∂ s x y = Σ_z (-1) ^ (ind x - ind z) ι_* (s x z × s z y)`.

A representing chain system of Barraud and Cornea is such a system in which, moreover, each
`s x y` represents the fundamental class of `M x y` relative to its boundary.

Let `G` be a topological monoid, for instance a Moore loop space, and let `q x y : M x y → G` be
**multiplicative** evaluation maps: `q x y (ι x z y (u, v)) = q x z u * q z y v`. Pushing the
chains forward gives a matrix `q_* s x y` in the DG algebra `C_*(G)` of normalized cubical chains
with the Pontryagin product. Since the push-forward commutes with boundaries and turns the face
pairings into Pontryagin products, the matrix is a twisting cocycle
(`TauCeti.ProductFaceChainSystem.twistingCocycle`). This is how the trajectory spaces of a Morse
function produce the Barraud–Cornea cocycle over the chains on the based loop space.

The construction is natural in `G`: composing the evaluation maps with a continuous monoid
homomorphism `φ` maps the twisting cocycle along the DG algebra morphism induced by `φ`
(`TauCeti.ProductFaceChainSystem.twistingCocycle_comp`).

## Main definitions

* `TauCeti.cubicalChainPushforward R f`: the push-forward `C_*(X) → C_*(Y)` of all normalized
  cubical chains along a continuous map `f`.
* `TauCeti.cubicalChainCross R f`: the pairing `C_*(X) × C_*(Y) → C_*(Z)`, `(a, b) ↦ f_* (a × b)`,
  induced by a continuous map `f : X × Y → Z`.
* `TauCeti.ProductFaceChainSystem`: chains whose boundaries decompose along product faces.
* `TauCeti.ProductFaceChainSystem.twistingCocycle`: the twisting cocycle obtained by evaluation.

## Main results

* `TauCeti.cubicalChainDifferential_cubicalChainPushforward`: the push-forward commutes with the
  boundary.
* `TauCeti.cubicalChainPushforward_cubicalChainCross`: the push-forward along a multiplicative
  evaluation turns the pairing into the Pontryagin product.
* `TauCeti.ProductFaceChainSystem.twistingCocycle_m`: the entries of the evaluated cocycle.
* `TauCeti.ProductFaceChainSystem.twistingCocycle_comp`: naturality in the monoid.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

open DirectSum

namespace TauCeti

open NormalizedCubicalChain

section Pushforward

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (R : Type*) [CommRing R]

/-- The **push-forward of normalized cubical chains** along a continuous map `f : X → Y`, in all
dimensions at once. It is the map `TauCeti.cubicalChainModuleLinearMap` of the chain modules, on
the direct sum of chains itself, so that it can land in the algebra of chains of a monoid. -/
def cubicalChainPushforward (f : C(X, Y)) :
    normalizedCubicalChainAlgebra X R →ₗ[R] normalizedCubicalChainAlgebra Y R :=
  DirectSum.toModule R ℕ _ fun n ↦ cubicalChainLof Y R n ∘ₗ map R f n

variable {R}

/-- The push-forward of a chain of dimension `n`. -/
@[simp]
theorem cubicalChainPushforward_lof (f : C(X, Y)) (n : ℕ) (c : NormalizedCubicalChain X R n) :
    cubicalChainPushforward R f (cubicalChainLof X R n c) = cubicalChainLof Y R n (map R f n c) :=
  DirectSum.toModule_lof R n c

/-- The push-forward along the identity is the identity. -/
@[simp]
theorem cubicalChainPushforward_id (a : normalizedCubicalChainAlgebra X R) :
    cubicalChainPushforward R (ContinuousMap.id X) a = a := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of n c =>
    rw [← DirectSum.lof_eq_of R, cubicalChainPushforward_lof, NormalizedCubicalChain.map_id,
      LinearMap.id_apply]
  | add a b ha hb => rw [map_add, ha, hb]

/-- The push-forward along a composite is the composite of the push-forwards. -/
theorem cubicalChainPushforward_comp (g : C(Y, Z)) (f : C(X, Y))
    (a : normalizedCubicalChainAlgebra X R) :
    cubicalChainPushforward R (g.comp f) a =
      cubicalChainPushforward R g (cubicalChainPushforward R f a) := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n c =>
    rw [← DirectSum.lof_eq_of R, cubicalChainPushforward_lof, cubicalChainPushforward_lof,
      cubicalChainPushforward_lof, NormalizedCubicalChain.map_comp, LinearMap.comp_apply]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

/-- The normalized cubical chains vanish in positive cohomological degrees. -/
theorem cubicalChainGrading_eq_bot_of_pos {i : ℤ} (hi : 0 < i) : cubicalChainGrading X R i = ⊥ :=
  eq_bot_iff.2 fun a ha ↦ by
    rcases (mem_cubicalChainGrading_iff X R).1 ha with h | ⟨n, c, hn, -⟩
    · exact (Submodule.mem_bot R).2 h
    · omega

/-- The push-forward preserves the cohomological degree. -/
theorem cubicalChainPushforward_mem (f : C(X, Y)) {i : ℤ} {a : normalizedCubicalChainAlgebra X R}
    (ha : a ∈ cubicalChainGrading X R i) :
    cubicalChainPushforward R f a ∈ cubicalChainGrading Y R i := by
  rcases (mem_cubicalChainGrading_iff X R).1 ha with rfl | ⟨n, c, hn, rfl⟩
  · rw [map_zero]
    exact zero_mem _
  · rw [cubicalChainPushforward_lof]
    exact (mem_cubicalChainGrading_iff Y R).2 (Or.inr ⟨n, _, hn, rfl⟩)

/-- The push-forward commutes with the boundary. -/
theorem cubicalChainDifferential_cubicalChainPushforward (f : C(X, Y))
    (a : normalizedCubicalChainAlgebra X R) :
    cubicalChainDifferential Y R (cubicalChainPushforward R f a) =
      cubicalChainPushforward R f (cubicalChainDifferential X R a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n c =>
    rw [← DirectSum.lof_eq_of R, cubicalChainPushforward_lof]
    rcases n with _ | k
    · rw [cubicalChainDifferential_lof_zero, cubicalChainDifferential_lof_zero, map_zero]
    · rw [cubicalChainDifferential_lof_succ, cubicalChainDifferential_lof_succ,
        cubicalChainPushforward_lof, ← LinearMap.comp_apply (boundary Y R k), ← map_boundary,
        LinearMap.comp_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- For a continuous monoid homomorphism, the push-forward is the induced morphism of DG
algebras. -/
theorem cubicalChainDGAlgHom_apply_eq_cubicalChainPushforward {G G' : Type*} [Monoid G]
    [TopologicalSpace G] [ContinuousMul G] [Monoid G'] [TopologicalSpace G'] [ContinuousMul G']
    (φ : G →ₜ* G') (a : normalizedCubicalChainAlgebra G R) :
    cubicalChainDGAlgHom R φ a = cubicalChainPushforward R φ.toContinuousMap a := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n c => rw [← DirectSum.lof_eq_of R, cubicalChainDGAlgHom_lof, cubicalChainPushforward_lof]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

variable (R) in
/-- The **pairing of chains induced by a map** `f : X × Y → Z`: the push-forward of the cross
product, `(a, b) ↦ f_* (a × b)`. It is the pairing `TauCeti.cubicalChainPairing` of the chain
modules, on spaces carrying no monoid action. -/
def cubicalChainCross (f : C(X × Y, Z)) :
    normalizedCubicalChainAlgebra X R →ₗ[R] normalizedCubicalChainAlgebra Y R →ₗ[R]
      normalizedCubicalChainAlgebra Z R :=
  ((cubicalChainPairing PUnit.{1} PUnit.{1} R f).compl₁₂
      (cubicalChainModuleEquiv X PUnit.{1} R).symm.toLinearMap
      (cubicalChainModuleEquiv Y PUnit.{1} R).symm.toLinearMap).compr₂
    (cubicalChainModuleEquiv Z PUnit.{1} R).toLinearMap

/-- The inverse of the identification of the chain module with the direct sum, on a homogeneous
chain. -/
private theorem cubicalChainModuleEquiv_symm_lof {n : ℕ} (c : NormalizedCubicalChain X R n) :
    (cubicalChainModuleEquiv X PUnit.{1} R).symm (cubicalChainLof X R n c) =
      cubicalChainModuleLof X PUnit.{1} R n c :=
  (LinearEquiv.symm_apply_eq _).2 (cubicalChainModuleEquiv_lof c).symm

/-- The pairing of homogeneous chains is the push-forward of their cross product. -/
@[simp]
theorem cubicalChainCross_lof_lof (f : C(X × Y, Z)) {p q : ℕ} (a : NormalizedCubicalChain X R p)
    (b : NormalizedCubicalChain Y R q) :
    cubicalChainCross R f (cubicalChainLof X R p a) (cubicalChainLof Y R q b) =
      cubicalChainLof Z R (p + q) (map R f (p + q) (crossProduct X Y R p q a b)) := by
  rw [cubicalChainCross, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, cubicalChainModuleEquiv_symm_lof,
    cubicalChainModuleEquiv_symm_lof, cubicalChainPairing_lof_lof, cubicalChainModuleEquiv_lof]

/-- The pairing adds cohomological degrees. -/
theorem cubicalChainCross_mem (f : C(X × Y, Z)) {i j : ℤ} {a : normalizedCubicalChainAlgebra X R}
    {b : normalizedCubicalChainAlgebra Y R} (ha : a ∈ cubicalChainGrading X R i)
    (hb : b ∈ cubicalChainGrading Y R j) :
    cubicalChainCross R f a b ∈ cubicalChainGrading Z R (i + j) := by
  have h := cubicalChainPairing_mem (H := PUnit.{1}) (K := PUnit.{1}) (R := R) f
    (m := (cubicalChainModuleEquiv X PUnit.{1} R).symm a)
    (n := (cubicalChainModuleEquiv Y PUnit.{1} R).symm b)
    (mem_cubicalChainModuleGrading.2 (by rwa [LinearEquiv.apply_symm_apply]))
    (mem_cubicalChainModuleGrading.2 (by rwa [LinearEquiv.apply_symm_apply]))
  exact mem_cubicalChainModuleGrading.1 h

/-- **Push-forward along a multiplicative evaluation.** If evaluation maps `qX`, `qY` and `qZ`
into a topological monoid satisfy `qZ (f (x, y)) = qX x * qY y`, then pushing the pairing induced
by `f` forward along `qZ` gives the Pontryagin product of the push-forwards. -/
theorem cubicalChainPushforward_cubicalChainCross {G : Type*} [Monoid G] [TopologicalSpace G]
    [ContinuousMul G] (f : C(X × Y, Z)) {qX : C(X, G)} {qY : C(Y, G)} {qZ : C(Z, G)}
    (hq : ∀ x y, qZ (f (x, y)) = qX x * qY y) (a : normalizedCubicalChainAlgebra X R)
    (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainPushforward R qZ (cubicalChainCross R f a b) =
      cubicalChainPushforward R qX a * cubicalChainPushforward R qY b := by
  have hcomp : qZ.comp f = (mulMap G).comp (qX.prodMap qY) :=
    ContinuousMap.ext fun z ↦ by simpa using hq z.1 z.2
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [map_add, LinearMap.add_apply, map_add, ha, ha', map_add, add_mul]
  | of p a =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b b' hb hb' => rw [map_add, map_add, hb, hb', map_add, mul_add]
    | of q b =>
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, cubicalChainCross_lof_lof,
        cubicalChainPushforward_lof, cubicalChainPushforward_lof, cubicalChainPushforward_lof,
        cubicalChainLof_mul, mul_def, ← map_crossProduct, ← LinearMap.comp_apply (map R qZ _),
        ← NormalizedCubicalChain.map_comp, hcomp, NormalizedCubicalChain.map_comp,
        LinearMap.comp_apply]

end Pushforward

/-! ### Product-face chain systems -/

universe uP uM uR

variable {R : Type uR} [CommRing R] {P : Type uP} [Fintype P] {ind : P → ℤ}
  {M : P → P → Type uM} [∀ x y, TopologicalSpace (M x y)]

variable (R ind) in
/-- A **product-face chain system** for the face maps `ι x z y : M x z × M z y → M x y`: normalized
cubical chains `s x y` on `M x y`, of dimension `ind x - ind y - 1` (cohomological degree
`ind y - ind x + 1`), whose boundaries decompose along the faces,
`∂ s x y = Σ_z (-1) ^ (ind x - ind z) ι_* (s x z × s z y)`.

For the compactified trajectory spaces of a Morse function, with `ι` the inclusion of broken
trajectories, a representing chain system of Barraud and Cornea is such a system whose chains
moreover represent the fundamental classes of the trajectory spaces relative to their boundaries.
-/
@[ext]
structure ProductFaceChainSystem (ι : ∀ x z y, C(M x z × M z y, M x y)) where
  /-- The chain on `M x y`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (M x y) R
  /-- The chain on `M x y` has dimension `ind x - ind y - 1`. -/
  chain_mem : ∀ x y, chain x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)
  /-- The boundary of each chain is the signed sum of the products of chains along the faces. -/
  differential_chain : ∀ x y, cubicalChainDifferential (M x y) R (chain x y) =
    ∑ z, (ind x - ind z).negOnePow • cubicalChainCross R (ι x z y) (chain x z) (chain z y)

namespace ProductFaceChainSystem

variable {ι : ∀ x z y, C(M x z × M z y, M x y)}

/-- The chains of a product-face chain system vanish when `ind x ≤ ind y`: they would have negative
dimension. -/
theorem chain_eq_zero_of_le (s : ProductFaceChainSystem R ind ι) {x y : P} (hxy : ind x ≤ ind y) :
    s.chain x y = 0 := by
  rcases (mem_cubicalChainGrading_iff _ R).1 (s.chain_mem x y) with h | ⟨n, c, hn, -⟩
  · exact h
  · omega

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]

/-- **The twisting cocycle of a product-face chain system.** Evaluation maps
`q x y : M x y → G` into a topological monoid that are multiplicative along the faces,
`q x y (ι x z y (u, v)) = q x z u * q z y v`, push the chain system forward to a twisting cocycle
`q_* s x y` over the DG algebra `C_*(G)`. For the trajectory spaces of a Morse function evaluated
into the Moore loop space, this is the Barraud–Cornea cocycle. -/
def twistingCocycle (s : ProductFaceChainSystem R ind ι) (q : ∀ x y, C(M x y, G))
    (hq : ∀ x z y u v, q x y (ι x z y (u, v)) = q x z u * q z y v) :
    TwistingCocycle (R := R) (A := normalizedCubicalChainAlgebra G R) (cubicalChainGrading G R)
      (cubicalChainDifferential G R) P ind :=
  .ofNonpos (fun x y ↦ cubicalChainPushforward R (q x y) (s.chain x y))
    (fun x y ↦ cubicalChainPushforward_mem (q x y) (s.chain_mem x y))
    (fun x y ↦ by
      rw [cubicalChainDifferential_cubicalChainPushforward, s.differential_chain, map_sum]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [map_zsmul_unit, cubicalChainPushforward_cubicalChainCross (ι x z y) (hq x z y)])
    fun _ ↦ cubicalChainGrading_eq_bot_of_pos

/-- The entries of the twisting cocycle of a product-face chain system are the push-forwards of
its chains. -/
@[simp]
theorem twistingCocycle_m (s : ProductFaceChainSystem R ind ι) (q : ∀ x y, C(M x y, G))
    (hq : ∀ x z y u v, q x y (ι x z y (u, v)) = q x z u * q z y v) (x y : P) :
    (s.twistingCocycle q hq).m x y = cubicalChainPushforward R (q x y) (s.chain x y) := by
  rw [twistingCocycle, TwistingCocycle.ofNonpos_m]

/-- **Naturality of the twisting cocycle in the monoid.** Composing multiplicative evaluation maps
with a continuous monoid homomorphism `φ` maps the twisting cocycle along the DG algebra morphism
`C_*(φ)`. -/
theorem twistingCocycle_comp {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ContinuousMul G']
    (s : ProductFaceChainSystem R ind ι) (q : ∀ x y, C(M x y, G))
    (hq : ∀ x z y u v, q x y (ι x z y (u, v)) = q x z u * q z y v) (φ : G →ₜ* G') :
    s.twistingCocycle (fun x y ↦ φ.toContinuousMap.comp (q x y))
        (fun x z y u v ↦ by simp [hq]) =
      (s.twistingCocycle q hq).map (cubicalChainDGAlgHom R φ) := by
  refine TwistingCocycle.ext fun x y ↦ ?_
  rw [twistingCocycle_m, TwistingCocycle.map_m, twistingCocycle_m, cubicalChainPushforward_comp]
  exact (cubicalChainDGAlgHom_apply_eq_cubicalChainPushforward φ _).symm

end ProductFaceChainSystem

end TauCeti
