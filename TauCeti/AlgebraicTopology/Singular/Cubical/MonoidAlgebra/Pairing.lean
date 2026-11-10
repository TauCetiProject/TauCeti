/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Lift

/-!
# Chain bimodule maps induced by balanced maps of spaces

Let `G`, `H` and `K` be topological monoids, `X` a `(G, H)`-space, `Y` an `(H, K)`-space and `Z`
a `(G, K)`-space, the actions being continuous and strict. A continuous map `f : X × Y → Z` gives
a pairing of normalized cubical chains, the push-forward of the cross product:
`c ⊗ c' ↦ f_* (c × c') : C^□_{p + q}(Z; R)` for `c ∈ C^□_p(X; R)` and `c' ∈ C^□_q(Y; R)`.
The boundary is a derivation for it with the Koszul sign.

When `f` is balanced over `H`, `f (x · h, y) = f (x, h · y)`, the pairing is balanced over the
chains of `H`, so it descends to the tensor product `C_*(X) ⊗_{C_*(H)} C_*(Y)`. When moreover `f`
is equivariant for `G` on the left and for `K` on the right, the induced map is a morphism of
differential graded `(C_*(G), C_*(K))`-bimodules
`C_*(X) ⊗_{C_*(H)} C_*(Y) → C_*(Z)`.

The basic example is concatenation of Moore paths, which induces the composition maps of the
chain bimodules of paths that change the basepoint of a DG local system.

The pairing is also stated on the plain direct sums `⨁ n, C^□_n(X; R)` of spaces carrying no
action (`TauCeti.cubicalChainSumPairing`), with the Leibniz rule, associativity and naturality for
the push-forward `TauCeti.cubicalChainSumMap`. For the multiplication of a topological monoid the
pairing is the Pontryagin product. These are the
operations of the chain systems of trajectory spaces in Morse theory.

## Main definitions

* `TauCeti.cubicalChainPairing H K R f`: the pairing `C_*(X) × C_*(Y) → C_*(Z)` induced by `f`.
* `TauCeti.cubicalChainTensorHom f hf hfG hfK`: the morphism of DG bimodules
  `C_*(X) ⊗_{C_*(H)} C_*(Y) → C_*(Z)` induced by a balanced equivariant map.
* `TauCeti.cubicalChainSumPairing R f`: the pairing on the direct sums of chains.

## Main results

* `TauCeti.cubicalChainModuleDifferential_cubicalChainPairing`: the Leibniz rule.
* `TauCeti.cubicalChainPairing_assoc`: pairings of pointwise associative maps are associative.
* `TauCeti.cubicalChainPairing_op_smul_left`: the pairing of a balanced map is balanced.
* `TauCeti.cubicalChainPairing_smul_left`, `TauCeti.cubicalChainPairing_op_smul_right`: the
  pairing of an equivariant map is equivariant.
* `TauCeti.cubicalChainTensorHom_tmul`: the induced morphism is the pairing on pure tensors.
* `TauCeti.cubicalChainDifferential_cubicalChainSumPairing`,
  `TauCeti.cubicalChainSumPairing_assoc`, `TauCeti.cubicalChainSumPairing_mulMap`: the Leibniz
  rule, associativity, and the Pontryagin product.
* `TauCeti.cubicalChainSumMap_cubicalChainSumPairing_of_comp`,
  `TauCeti.cubicalChainSumMap_cubicalChainSumPairing_of_mul`: push-forward of a pairing along a
  map compatible with another pairing, or multiplicative into a topological monoid.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite DirectSum

namespace TauCeti

open NormalizedCubicalChain

section Pairing

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (H K R : Type*) [CommRing R]

/-- The **pairing of chain modules induced by a map** `f : X × Y → Z`: the push-forward of the
cross product, `c ⊗ c' ↦ f_* (c × c')`. The monoids `H` and `K` are the phantom parameters of
`TauCeti.cubicalChainModule`, recording the right actions on `X` and on `Y` and `Z`. -/
def cubicalChainPairing (f : C(X × Y, Z)) :
    cubicalChainModule X H R →ₗ[R] cubicalChainModule Y K R →ₗ[R] cubicalChainModule Z K R :=
  cubicalChainModuleDesc fun p ↦ (cubicalChainModuleDesc fun q ↦
    ((crossProduct X Y R p q).compr₂
      ((cubicalChainModuleLof Z K R (p + q)).comp (map R f (p + q)))).flip).flip

variable {H K R}

/-- The pairing on homogeneous chains is the push-forward of their cross product. -/
@[simp]
theorem cubicalChainPairing_lof_lof (f : C(X × Y, Z)) {p q : ℕ}
    (c : NormalizedCubicalChain X R p) (c' : NormalizedCubicalChain Y R q) :
    cubicalChainPairing H K R f (cubicalChainModuleLof X H R p c)
        (cubicalChainModuleLof Y K R q c') =
      cubicalChainModuleLof Z K R (p + q) (map R f (p + q) (crossProduct X Y R p q c c')) := by
  rw [cubicalChainPairing, cubicalChainModuleDesc_lof, LinearMap.flip_apply,
    cubicalChainModuleDesc_lof]
  rfl

/-- **Associativity of pairings**: two ways of combining three factors that agree pointwise,
`g (f (x, y), w) = g' (x, f' (y, w))`, give the same pairing of chains. -/
theorem cubicalChainPairing_assoc {L W U T V : Type*} [TopologicalSpace W] [TopologicalSpace U]
    [TopologicalSpace T] [TopologicalSpace V] {f : C(X × Y, U)} {g : C(U × W, V)}
    {f' : C(Y × W, T)} {g' : C(X × T, V)} (h : ∀ x y w, g (f (x, y), w) = g' (x, f' (y, w)))
    (m : cubicalChainModule X H R) (n : cubicalChainModule Y K R) (o : cubicalChainModule W L R) :
    cubicalChainPairing K L R g (cubicalChainPairing H K R f m n) o =
      cubicalChainPairing H L R g' m (cubicalChainPairing K L R f' n o) := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => simp only [map_add, LinearMap.add_apply, hm, hm']
  | lof p c =>
    induction n using cubicalChainModule.induction_on with
    | zero => simp
    | add n n' hn hn' => simp only [map_add, LinearMap.add_apply, hn, hn']
    | lof q c' =>
      induction o using cubicalChainModule.induction_on with
      | zero => simp
      | add o o' ho ho' => simp only [map_add, ho, ho']
      | lof r c'' =>
        rw [cubicalChainPairing_lof_lof, cubicalChainPairing_lof_lof, cubicalChainPairing_lof_lof,
          cubicalChainPairing_lof_lof, ← cubicalChainModuleLof_cast (Nat.add_assoc p q r)]
        congr 1
        refine map_crossProduct_map_assoc R ?_ c c' c''
        ext ⟨⟨x, y⟩, w⟩
        simp [Homeomorph.prodAssoc, Equiv.prodAssoc, h]

/-- The pairing adds cohomological degrees. -/
theorem cubicalChainPairing_mem (f : C(X × Y, Z)) {i j : ℤ} {m : cubicalChainModule X H R}
    {n : cubicalChainModule Y K R} (hm : m ∈ cubicalChainModuleGrading X H R i)
    (hn : n ∈ cubicalChainModuleGrading Y K R j) :
    cubicalChainPairing H K R f m n ∈ cubicalChainModuleGrading Z K R (i + j) := by
  rcases mem_cubicalChainModuleGrading_iff.1 hm with rfl | ⟨p, c, hp, rfl⟩
  · rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  rcases mem_cubicalChainModuleGrading_iff.1 hn with rfl | ⟨q, c', hq, rfl⟩
  · rw [map_zero]
    exact zero_mem _
  rw [cubicalChainPairing_lof_lof]
  exact mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨p + q, _, by push_cast; omega, rfl⟩)

private theorem boundary_map_crossProduct (f : C(X × Y, Z)) {p q : ℕ}
    (c : NormalizedCubicalChain X R (p + 1)) (c' : NormalizedCubicalChain Y R (q + 1)) :
    boundary Z R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
          (map R f ((p + 1) + (q + 1)) (crossProduct X Y R (p + 1) (q + 1) c c'))) =
      map R f (p + (q + 1)) (crossProduct X Y R p (q + 1) (boundary X R p c) c') +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (map R f ((p + 1) + q) (crossProduct X Y R (p + 1) q c (boundary Y R q c'))) := by
  rw [← map_cast, ← LinearMap.comp_apply (boundary Z R _), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct, map_add, map_smul, map_cast]
  rfl

private theorem boundary_map_crossProduct_zero_right (f : C(X × Y, Z)) {p : ℕ}
    (c : NormalizedCubicalChain X R (p + 1)) (c' : NormalizedCubicalChain Y R 0) :
    boundary Z R p (map R f ((p + 1) + 0) (crossProduct X Y R (p + 1) 0 c c')) =
      map R f (p + 0) (crossProduct X Y R p 0 (boundary X R p c) c') := by
  rw [← LinearMap.comp_apply (boundary Z R p), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_right]
  rfl

private theorem boundary_map_crossProduct_zero_left (f : C(X × Y, Z)) {q : ℕ}
    (c : NormalizedCubicalChain X R 0) (c' : NormalizedCubicalChain Y R (q + 1)) :
    boundary Z R q (cast R (Nat.zero_add (q + 1))
        (map R f (0 + (q + 1)) (crossProduct X Y R 0 (q + 1) c c'))) =
      cast R (Nat.zero_add q) (map R f (0 + q) (crossProduct X Y R 0 q c (boundary Y R q c'))) := by
  rw [← map_cast, ← LinearMap.comp_apply (boundary Z R q), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_left, map_cast]

/-- **The Leibniz rule for the pairing** on homogeneous chains:
`∂ (c ⊗ c') = ∂ c ⊗ c' + (-1) ^ p • (c ⊗ ∂ c')` for `c` of dimension `p`. -/
theorem cubicalChainModuleDifferential_cubicalChainPairing_lof (f : C(X × Y, Z)) {p q : ℕ}
    (c : NormalizedCubicalChain X R p) (c' : NormalizedCubicalChain Y R q) :
    cubicalChainModuleDifferential Z K R
        (cubicalChainPairing H K R f (cubicalChainModuleLof X H R p c)
          (cubicalChainModuleLof Y K R q c')) =
      cubicalChainPairing H K R f
          (cubicalChainModuleDifferential X H R (cubicalChainModuleLof X H R p c))
          (cubicalChainModuleLof Y K R q c') +
        (-(p : ℤ)).negOnePow • cubicalChainPairing H K R f (cubicalChainModuleLof X H R p c)
          (cubicalChainModuleDifferential Y K R (cubicalChainModuleLof Y K R q c')) := by
  rw [cubicalChainPairing_lof_lof, negOnePow_neg_natCast_smul_cubicalChainModule]
  -- In each case the dimension of the pairing reduces definitionally to `0` or to a successor,
  -- so the differential is computed by `cubicalChainModuleDifferential_lof_zero` or `_succ`.
  rcases p with _ | k <;> rcases q with _ | j
  · rw [cubicalChainModuleDifferential_lof_zero, cubicalChainModuleDifferential_lof_zero,
      cubicalChainModuleDifferential_lof_zero, map_zero, map_zero, LinearMap.zero_apply,
      smul_zero, zero_add]
  · have hL : cubicalChainModuleDifferential Z K R
        (cubicalChainModuleLof Z K R (0 + (j + 1))
          (map R f (0 + (j + 1)) (crossProduct X Y R 0 (j + 1) c c'))) =
          cubicalChainModuleLof Z K R (0 + j)
            (map R f (0 + j) (crossProduct X Y R 0 j c (boundary Y R j c'))) := by
      refine (cubicalChainModuleDifferential_lof_succ (0 + j) _).trans ?_
      congr 1
      apply cast_injective R (Nat.zero_add j)
      exact (boundary_cast R (Nat.zero_add j) _).symm.trans
        (boundary_map_crossProduct_zero_left f c c')
    rw [hL, cubicalChainModuleDifferential_lof_zero, cubicalChainModuleDifferential_lof_succ,
      cubicalChainPairing_lof_lof, map_zero, LinearMap.zero_apply,
      zero_add (M := cubicalChainModule Z K R), pow_zero, one_smul]
  · refine (cubicalChainModuleDifferential_lof_succ k _).trans ?_
    rw [boundary_map_crossProduct_zero_right, cubicalChainModuleDifferential_lof_succ,
      cubicalChainModuleDifferential_lof_zero, map_zero, cubicalChainPairing_lof_lof,
      smul_zero, add_zero (M := cubicalChainModule Z K R)]
    rfl
  · refine (cubicalChainModuleDifferential_lof_succ (k + 1 + j) _).trans ?_
    have h' : k + 1 + j = k + j + 1 := by omega
    have e : cast R h' (boundary Z R (k + 1 + j)
        (map R f (k + 1 + (j + 1)) (crossProduct X Y R (k + 1) (j + 1) c c'))) =
        map R f (k + (j + 1)) (crossProduct X Y R k (j + 1) (boundary X R k c) c') +
          (-1 : R) ^ (k + 1) • cast R h'
            (map R f (k + 1 + j) (crossProduct X Y R (k + 1) j c (boundary Y R j c'))) :=
      (boundary_cast R h' _).symm.trans (boundary_map_crossProduct f c c')
    rw [cubicalChainModuleDifferential_lof_succ, cubicalChainModuleDifferential_lof_succ,
      cubicalChainPairing_lof_lof, cubicalChainPairing_lof_lof,
      ← cubicalChainModuleLof_cast h', e, map_add, map_smul, cubicalChainModuleLof_cast]
    rfl

/-- **The Leibniz rule for the pairing**: for `m` of cohomological degree `i`,
`d (m ⊗ n) = d m ⊗ n + (-1) ^ i • (m ⊗ d n)`. -/
theorem cubicalChainModuleDifferential_cubicalChainPairing (f : C(X × Y, Z)) {i : ℤ}
    {m : cubicalChainModule X H R} (hm : m ∈ cubicalChainModuleGrading X H R i)
    (n : cubicalChainModule Y K R) :
    cubicalChainModuleDifferential Z K R (cubicalChainPairing H K R f m n) =
      cubicalChainPairing H K R f (cubicalChainModuleDifferential X H R m) n +
        i.negOnePow • cubicalChainPairing H K R f m (cubicalChainModuleDifferential Y K R n) := by
  rcases mem_cubicalChainModuleGrading_iff.1 hm with rfl | ⟨p, c, hp, rfl⟩
  · simp
  obtain rfl : i = -(p : ℤ) := by omega
  induction n using cubicalChainModule.induction_on with
  | zero => simp
  | lof q c' => exact cubicalChainModuleDifferential_cubicalChainPairing_lof f c c'
  | add n n' hn hn' =>
    simp only [map_add, hn, hn', smul_add]
    abel

end Pairing

section Equivariance

variable {G H K X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {R : Type*} [CommRing R]

/-- **The pairing of a balanced map is balanced**: if `f (x · h, y) = f (x, h · y)`, then
`(m · a) ⊗ n = m ⊗ (a · n)` for chains `a` of `H`. -/
theorem cubicalChainPairing_op_smul_left [Monoid H] [TopologicalSpace H] [ContinuousMul H]
    [MulAction Hᵐᵒᵖ X] [ContinuousSMul Hᵐᵒᵖ X]
    [MulAction H Y] [ContinuousSMul H Y] (f : C(X × Y, Z))
    (hf : ∀ (h : H) (x : X) (y : Y), f (op h • x, y) = f (x, h • y))
    (a : normalizedCubicalChainAlgebra H R) (m : cubicalChainModule X H R)
    (n : cubicalChainModule Y K R) :
    cubicalChainPairing H K R f (op a • m) n = cubicalChainPairing H K R f m (a • n) := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => simp only [smul_add, map_add, LinearMap.add_apply, hm, hm']
  | lof p c =>
    induction n using cubicalChainModule.induction_on with
    | zero => simp
    | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
    | lof q c' =>
      induction a using DirectSum.induction_on with
      | zero => simp
      | add a a' ha ha' =>
        rw [MulOpposite.op_add, add_smul, map_add, LinearMap.add_apply, ha, ha', add_smul, map_add]
      | of r z =>
        rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof,
          lof_smul_cubicalChainModuleLof, cubicalChainPairing_lof_lof,
          cubicalChainPairing_lof_lof, ← cubicalChainModuleLof_cast (Nat.add_assoc p r q)]
        congr 1
        simp only [act_def, leftAct_def]
        refine map_crossProduct_map_assoc R ?_ c z c'
        ext ⟨⟨x, y⟩, w⟩
        simp [Homeomorph.prodAssoc, Equiv.prodAssoc, hf]

/-- **The pairing of a left-equivariant map is left-equivariant**: if
`f (g · x, y) = g · f (x, y)`, then `(a · m) ⊗ n = a · (m ⊗ n)` for chains `a` of `G`. -/
theorem cubicalChainPairing_smul_left [Monoid G] [TopologicalSpace G] [ContinuousMul G]
    [MulAction G X] [ContinuousSMul G X] [MulAction G Z]
    [ContinuousSMul G Z] (f : C(X × Y, Z))
    (hf : ∀ (g : G) (x : X) (y : Y), f (g • x, y) = g • f (x, y))
    (a : normalizedCubicalChainAlgebra G R) (m : cubicalChainModule X H R)
    (n : cubicalChainModule Y K R) :
    cubicalChainPairing H K R f (a • m) n = a • cubicalChainPairing H K R f m n := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => simp only [smul_add, map_add, LinearMap.add_apply, hm, hm']
  | lof p c =>
    induction n using cubicalChainModule.induction_on with
    | zero => simp
    | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
    | lof q c' =>
      induction a using DirectSum.induction_on with
      | zero => simp
      | add a a' ha ha' => simp only [add_smul, map_add, LinearMap.add_apply, ha, ha']
      | of r z =>
        rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof, cubicalChainPairing_lof_lof,
          cubicalChainPairing_lof_lof, lof_smul_cubicalChainModuleLof,
          ← cubicalChainModuleLof_cast (Nat.add_assoc r p q)]
        congr 1
        simp only [leftAct_def]
        refine map_crossProduct_map_assoc R ?_ z c c'
        ext ⟨⟨x, y⟩, w⟩
        simp [Homeomorph.prodAssoc, Equiv.prodAssoc, hf]

/-- **The pairing of a right-equivariant map is right-equivariant**: if
`f (x, y · k) = f (x, y) · k`, then `m ⊗ (n · a) = (m ⊗ n) · a` for chains `a` of `K`. -/
theorem cubicalChainPairing_op_smul_right [Monoid K] [TopologicalSpace K] [ContinuousMul K]
    [MulAction Kᵐᵒᵖ Y] [ContinuousSMul Kᵐᵒᵖ Y]
    [MulAction Kᵐᵒᵖ Z] [ContinuousSMul Kᵐᵒᵖ Z] (f : C(X × Y, Z))
    (hf : ∀ (k : K) (x : X) (y : Y), f (x, op k • y) = op k • f (x, y))
    (a : normalizedCubicalChainAlgebra K R) (m : cubicalChainModule X H R)
    (n : cubicalChainModule Y K R) :
    cubicalChainPairing H K R f m (op a • n) = op a • cubicalChainPairing H K R f m n := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => simp only [smul_add, map_add, LinearMap.add_apply, hm, hm']
  | lof p c =>
    induction n using cubicalChainModule.induction_on with
    | zero => simp
    | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
    | lof q c' =>
      induction a using DirectSum.induction_on with
      | zero => simp
      | add a a' ha ha' =>
        rw [MulOpposite.op_add, add_smul, map_add, ha, ha', add_smul]
      | of r z =>
        rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof,
          cubicalChainPairing_lof_lof, cubicalChainPairing_lof_lof,
          op_lof_smul_cubicalChainModuleLof, ← cubicalChainModuleLof_cast (Nat.add_assoc p q r)]
        congr 1
        simp only [act_def]
        refine (map_crossProduct_map_assoc R ?_ c c' z).symm
        ext ⟨⟨x, y⟩, w⟩
        simp [Homeomorph.prodAssoc, Equiv.prodAssoc, hf]

end Equivariance

section TensorHom

universe u

variable {G H K : Type*} {X Y Z : Type u} [Monoid G] [TopologicalSpace G]
  [ContinuousMul G] [Monoid H] [TopologicalSpace H] [ContinuousMul H] [Monoid K]
  [TopologicalSpace K] [ContinuousMul K] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [MulAction G X] [ContinuousSMul G X] [MulAction Hᵐᵒᵖ X]
  [ContinuousSMul Hᵐᵒᵖ X] [SMulCommClass G Hᵐᵒᵖ X] [MulAction H Y] [ContinuousSMul H Y]
  [MulAction Kᵐᵒᵖ Y] [ContinuousSMul Kᵐᵒᵖ Y] [SMulCommClass H Kᵐᵒᵖ Y] [MulAction G Z]
  [ContinuousSMul G Z] [MulAction Kᵐᵒᵖ Z] [ContinuousSMul Kᵐᵒᵖ Z] [SMulCommClass G Kᵐᵒᵖ Z]
  {R : Type*} [CommRing R]

/-- **The morphism of DG bimodules induced by a balanced equivariant map**
`f : X × Y → Z`: the map `C_*(X) ⊗_{C_*(H)} C_*(Y) → C_*(Z)`, `c ⊗ c' ↦ f_* (c × c')`. -/
def cubicalChainTensorHom (f : C(X × Y, Z))
    (hf : ∀ (h : H) (x : X) (y : Y), f (op h • x, y) = f (x, h • y))
    (hfG : ∀ (g : G) (x : X) (y : Y), f (g • x, y) = g • f (x, y))
    (hfK : ∀ (k : K) (x : X) (y : Y), f (x, op k • y) = op k • f (x, y)) :
    DGBimoduleCat.tensorObj (cubicalChainBimoduleDG G X H R) (cubicalChainBimoduleDG H Y K R) ⟶
      cubicalChainBimoduleDG G Z K R :=
  DGBimoduleCat.tensorLift (cubicalChainPairing H K R f) (cubicalChainPairing_op_smul_left f hf)
    (cubicalChainPairing_smul_left f hfG) (cubicalChainPairing_op_smul_right f hfK)
    (cubicalChainPairing_mem f) (cubicalChainModuleDifferential_cubicalChainPairing f)

/-- The induced morphism on a pure tensor is the pairing. -/
@[simp]
theorem cubicalChainTensorHom_tmul (f : C(X × Y, Z))
    (hf : ∀ (h : H) (x : X) (y : Y), f (op h • x, y) = f (x, h • y))
    (hfG : ∀ (g : G) (x : X) (y : Y), f (g • x, y) = g • f (x, y))
    (hfK : ∀ (k : K) (x : X) (y : Y), f (x, op k • y) = op k • f (x, y))
    (m : cubicalChainModule X H R) (n : cubicalChainModule Y K R) :
    cubicalChainTensorHom f hf hfG hfK
        (BalancedTensorProduct.tmul R (normalizedCubicalChainAlgebra H R) m n) =
      cubicalChainPairing H K R f m n :=
  DGBimoduleCat.tensorLift_tmul (M := cubicalChainBimoduleDG G X H R)
    (N := cubicalChainBimoduleDG H Y K R) (P := cubicalChainBimoduleDG G Z K R) _ _ _ _ _ _ m n

end TensorHom

section SumPairing

/-! ### Pairings of the direct sums of chains

The same construction on the plain direct sum `⨁ n, C^□_n(X; R)` of a space, with no action
recorded. -/

variable {X Y Z W U V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W] [TopologicalSpace U] [TopologicalSpace V] (R : Type*) [CommRing R]

/-- The **pairing of direct sums of chains induced by a map** `f : X × Y → Z`: the push-forward of
the cross product, `c ⊗ c' ↦ f_* (c × c')`. It is `TauCeti.cubicalChainPairing` read through the
equivalences of the chain modules with the direct sums, with the trivial monoid as the phantom
parameter. -/
def cubicalChainSumPairing (f : C(X × Y, Z)) :
    normalizedCubicalChainAlgebra X R →ₗ[R] normalizedCubicalChainAlgebra Y R →ₗ[R]
      normalizedCubicalChainAlgebra Z R :=
  ((cubicalChainPairing Unit Unit R f).compl₁₂
    (cubicalChainModuleEquiv X Unit R).symm.toLinearMap
    (cubicalChainModuleEquiv Y Unit R).symm.toLinearMap).compr₂
      (cubicalChainModuleEquiv Z Unit R).toLinearMap

variable {R}

/-- The pairing of direct sums is the pairing of chain modules, read through the equivalences. -/
theorem cubicalChainSumPairing_apply (f : C(X × Y, Z)) (a : normalizedCubicalChainAlgebra X R)
    (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainSumPairing R f a b = cubicalChainModuleEquiv Z Unit R
      (cubicalChainPairing Unit Unit R f ((cubicalChainModuleEquiv X Unit R).symm a)
        ((cubicalChainModuleEquiv Y Unit R).symm b)) :=
  (rfl)

/-- The pairing on homogeneous chains is the push-forward of their cross product. -/
@[simp]
theorem cubicalChainSumPairing_lof_lof (f : C(X × Y, Z)) {p q : ℕ}
    (c : NormalizedCubicalChain X R p) (c' : NormalizedCubicalChain Y R q) :
    cubicalChainSumPairing R f (cubicalChainLof X R p c) (cubicalChainLof Y R q c') =
      cubicalChainLof Z R (p + q) (map R f (p + q) (crossProduct X Y R p q c c')) := by
  rw [cubicalChainSumPairing_apply, cubicalChainModuleEquiv_symm_lof,
    cubicalChainModuleEquiv_symm_lof, cubicalChainPairing_lof_lof, cubicalChainModuleEquiv_lof]

/-- The pairing adds cohomological degrees. -/
theorem cubicalChainSumPairing_mem (f : C(X × Y, Z)) {i j : ℤ}
    {a : normalizedCubicalChainAlgebra X R} {b : normalizedCubicalChainAlgebra Y R}
    (ha : a ∈ cubicalChainGrading X R i) (hb : b ∈ cubicalChainGrading Y R j) :
    cubicalChainSumPairing R f a b ∈ cubicalChainGrading Z R (i + j) := by
  rw [cubicalChainSumPairing_apply]
  exact mem_cubicalChainModuleGrading.1 (cubicalChainPairing_mem f
    (mem_cubicalChainModuleGrading.2 (by rwa [LinearEquiv.apply_symm_apply]))
    (mem_cubicalChainModuleGrading.2 (by rwa [LinearEquiv.apply_symm_apply])))

/-- **The Leibniz rule for the pairing of direct sums**: for `a` of cohomological degree `i`,
`d (a ⊗ b) = d a ⊗ b + (-1) ^ i • (a ⊗ d b)`. -/
theorem cubicalChainDifferential_cubicalChainSumPairing (f : C(X × Y, Z)) {i : ℤ}
    {a : normalizedCubicalChainAlgebra X R} (ha : a ∈ cubicalChainGrading X R i)
    (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainDifferential Z R (cubicalChainSumPairing R f a b) =
      cubicalChainSumPairing R f (cubicalChainDifferential X R a) b +
        i.negOnePow • cubicalChainSumPairing R f a (cubicalChainDifferential Y R b) := by
  rw [cubicalChainSumPairing_apply, cubicalChainSumPairing_apply, cubicalChainSumPairing_apply,
    ← cubicalChainModuleEquiv_differential, cubicalChainModuleEquiv_symm_differential,
    cubicalChainModuleEquiv_symm_differential,
    cubicalChainModuleDifferential_cubicalChainPairing f
      (mem_cubicalChainModuleGrading.2 (by rwa [LinearEquiv.apply_symm_apply])),
    map_add, map_zsmul_unit]

/-- **Associativity of pairings of direct sums**: two ways of combining three factors that agree
pointwise, `g (f (x, y), w) = g' (x, f' (y, w))`, give the same pairing of chains. -/
theorem cubicalChainSumPairing_assoc {f : C(X × Y, U)} {g : C(U × W, V)} {f' : C(Y × W, Z)}
    {g' : C(X × Z, V)} (h : ∀ x y w, g (f (x, y), w) = g' (x, f' (y, w)))
    (a : normalizedCubicalChainAlgebra X R) (b : normalizedCubicalChainAlgebra Y R)
    (c : normalizedCubicalChainAlgebra W R) :
    cubicalChainSumPairing R g (cubicalChainSumPairing R f a b) c =
      cubicalChainSumPairing R g' a (cubicalChainSumPairing R f' b c) := by
  simp only [cubicalChainSumPairing_apply, LinearEquiv.symm_apply_apply]
  exact congrArg _ (cubicalChainPairing_assoc h _ _ _)

/-- **Naturality of the pairing on the left**: pushing a pairing forward along `g` is the pairing
of the composite map. -/
theorem cubicalChainSumMap_cubicalChainSumPairing (f : C(X × Y, Z)) (g : C(Z, W))
    (a : normalizedCubicalChainAlgebra X R) (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainSumMap R g (cubicalChainSumPairing R f a b) =
      cubicalChainSumPairing R (g.comp f) a b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [map_add, LinearMap.add_apply, map_add, ha, ha', map_add,
      LinearMap.add_apply]
  | of p c =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b b' hb hb' => rw [map_add, map_add, hb, hb', map_add]
    | of q c' =>
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, cubicalChainSumPairing_lof_lof,
        cubicalChainSumPairing_lof_lof, cubicalChainSumMap_lof, NormalizedCubicalChain.map_comp,
        LinearMap.comp_apply]

/-- **Naturality of the pairing on the right**: the pairing of `f ∘ (g × h)` is the pairing of `f`
on the push-forwards along `g` and `h`. -/
theorem cubicalChainSumPairing_comp_prodMap (f : C(Z × W, V)) (g : C(X, Z)) (h : C(Y, W))
    (a : normalizedCubicalChainAlgebra X R) (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainSumPairing R (f.comp (g.prodMap h)) a b =
      cubicalChainSumPairing R f (cubicalChainSumMap R g a) (cubicalChainSumMap R h b) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [map_add, LinearMap.add_apply, ha, ha', map_add, map_add,
      LinearMap.add_apply]
  | of p c =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b b' hb hb' => rw [map_add, hb, hb', map_add, map_add]
    | of q c' =>
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, cubicalChainSumPairing_lof_lof,
        cubicalChainSumMap_lof, cubicalChainSumMap_lof, cubicalChainSumPairing_lof_lof,
        NormalizedCubicalChain.map_comp, LinearMap.comp_apply, map_crossProduct]

/-- The pairing induced by the multiplication of a topological monoid is the Pontryagin product. -/
@[simp]
theorem cubicalChainSumPairing_mulMap {G : Type*} [Monoid G] [TopologicalSpace G]
    [ContinuousMul G] (a b : normalizedCubicalChainAlgebra G R) :
    cubicalChainSumPairing R (mulMap G) a b = a * b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [map_add, LinearMap.add_apply, ha, ha', add_mul]
  | of p c =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b b' hb hb' => rw [map_add, hb, hb', mul_add]
    | of q c' =>
      rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, cubicalChainSumPairing_lof_lof,
        cubicalChainLof_mul, mul_def]

/-- **Naturality of the pairing**: if `g (f (x, y)) = f' (h x, h' y)`, pushing the pairing of `f`
forward along `g` is the pairing of `f'` of the push-forwards along `h` and `h'`. -/
theorem cubicalChainSumMap_cubicalChainSumPairing_of_comp {X' Y' : Type*} [TopologicalSpace X']
    [TopologicalSpace Y'] {f : C(X × Y, Z)} {g : C(Z, W)} {f' : C(X' × Y', W)} {h : C(X, X')}
    {h' : C(Y, Y')} (hf : ∀ x y, g (f (x, y)) = f' (h x, h' y))
    (a : normalizedCubicalChainAlgebra X R) (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainSumMap R g (cubicalChainSumPairing R f a b) =
      cubicalChainSumPairing R f' (cubicalChainSumMap R h a) (cubicalChainSumMap R h' b) := by
  have hcomp : g.comp f = f'.comp (h.prodMap h') :=
    ContinuousMap.ext fun ⟨x, y⟩ ↦ by simpa using hf x y
  rw [cubicalChainSumMap_cubicalChainSumPairing, hcomp, cubicalChainSumPairing_comp_prodMap]

/-- If `g (f (x, y)) = h x * h' y` in a topological monoid `G`, pushing the pairing of `f`
forward along `g` is the Pontryagin product of the push-forwards along `h` and `h'`. -/
theorem cubicalChainSumMap_cubicalChainSumPairing_of_mul {G : Type*} [Monoid G]
    [TopologicalSpace G] [ContinuousMul G] {f : C(X × Y, Z)} {g : C(Z, G)} {h : C(X, G)}
    {h' : C(Y, G)} (hf : ∀ x y, g (f (x, y)) = h x * h' y) (a : normalizedCubicalChainAlgebra X R)
    (b : normalizedCubicalChainAlgebra Y R) :
    cubicalChainSumMap R g (cubicalChainSumPairing R f a b) =
      cubicalChainSumMap R h a * cubicalChainSumMap R h' b := by
  rw [cubicalChainSumMap_cubicalChainSumPairing_of_comp (f' := mulMap G) (by simpa using hf),
    cubicalChainSumPairing_mulMap]

end SumPairing

end TauCeti

end
