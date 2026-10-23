/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Hom
public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Twisting the chain algebra of a monoid by a path-constant character

Let `G` be a topological monoid and `χ : G →* R` a monoid homomorphism into the multiplicative
monoid of a commutative ring which is constant along paths (`Joined x y → χ x = χ y`).  Scaling
each singular cube `σ` by `χ (σ 0)`, the value of `χ` at its origin, is a linear endomorphism of
the cubical chains (`TauCeti.CubicalChain.twist`).  It preserves degenerate chains, so it descends
to the normalized chains, and it is a morphism of DG algebras of `C^□_*(G; R)`
(`TauCeti.cubicalChainTwist`):

* it fixes the unit, since the unit is the `0`-cube at `1` and `χ 1 = 1`;
* it is multiplicative, since the origin of a product cube is the product of the origins;
* it commutes with the boundary, since `χ` takes the same value at every point of a cube, the
  cube being path connected.

Twisting is multiplicative in the character (`TauCeti.cubicalChainTwist_mul`), so a
character with values in the units `Rˣ` gives an automorphism.  For the Moore loop space this is
the map `Φ^L` of the source's §2.3, attached to a rank-one local system `L`.

## Main definitions

* `TauCeti.CubicalChain.twist χ n`: the twist of unnormalized `n`-chains.
* `TauCeti.NormalizedCubicalChain.twist χ n`: the twist of normalized `n`-chains.
* `TauCeti.cubicalChainTwist χ hχ`: the twist as a morphism of DG algebras.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.3.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {G : Type*} [TopologicalSpace G] {R : Type*} [CommRing R]

namespace SingularCube

omit [CommRing R] in
/-- A function constant along paths takes the same value at every point of a singular cube. -/
theorem apply_eq_apply_zero_of_joined {Y : Type*} (w : G → Y)
    (hw : ∀ ⦃x y : G⦄, Joined x y → w x = w y) {n : ℕ} (c : SingularCube G n)
    (x : Fin n → I) : w (c x) = w (c 0) :=
  hw (Joined.map (⟨Path.pi fun j ↦ pathTowardZero (x j)⟩ : Joined x 0) c.continuous)

end SingularCube

namespace CubicalChain

variable (w : G → R)

/-- The **twist** of cubical `n`-chains by a weight `w : G → R`: a cube `σ` is scaled by the weight
`w (σ 0)` of its origin. -/
def twist (n : ℕ) : CubicalChain G R n →ₗ[R] CubicalChain G R n :=
  linearCombination R fun c ↦ single c (w (c 0))

@[simp]
theorem twist_single {n : ℕ} (c : SingularCube G n) (a : R) :
    twist w n (single c a) = single c (w (c 0) * a) := by
  rw [twist, linearCombination_single, smul_single, smul_eq_mul, mul_comm]

/-- The twist preserves the degenerate chains. -/
theorem twist_mem_degenerate {n : ℕ} {g : CubicalChain G R n}
    (hg : g ∈ degenerate G R n) : twist w n g ∈ degenerate G R n := by
  refine degenerate_induction (R := R) (P := fun g ↦ twist w n g ∈ degenerate G R n) ?_ ?_ ?_ ?_ hg
  · rw [map_zero]
    exact zero_mem _
  · intro c hc
    rw [twist_single]
    exact single_mem_degenerate R hc _
  · intro f g hf hg
    rw [map_add]
    exact add_mem hf hg
  · intro r f hf
    rw [map_smul]
    exact Submodule.smul_mem _ r hf

end CubicalChain

namespace NormalizedCubicalChain

variable (w : G → R)

/-- The twist of normalized cubical `n`-chains by a weight `w : G → R`. -/
def twist (n : ℕ) : NormalizedCubicalChain G R n →ₗ[R] NormalizedCubicalChain G R n :=
  Submodule.mapQ _ _ (CubicalChain.twist w n) fun _ ↦ CubicalChain.twist_mem_degenerate w

@[simp]
theorem twist_mk {n : ℕ} (g : CubicalChain G R n) :
    twist w n (Submodule.Quotient.mk g) = Submodule.Quotient.mk (CubicalChain.twist w n g) :=
  Submodule.mapQ_apply _ _ _ g

/-- The twist of the class of a cube scales it by the weight of its origin. -/
@[simp]
theorem twist_ofCube {n : ℕ} (c : SingularCube G n) :
    twist w n (ofCube G R c) = w (c 0) • ofCube G R c := by
  rw [ofCube_def, twist_mk, CubicalChain.twist_single, _root_.mul_one, ← Submodule.Quotient.mk_smul,
    smul_single_one]

/-- Twisting is multiplicative in the weight. -/
theorem twist_comp (w w' : G → R) (n : ℕ) :
    twist w n ∘ₗ twist w' n = twist (w * w') n :=
  linearMap_ext fun c ↦ by
    simp [smul_smul, mul_comm (w (c 0))]

/-- The twist by the constant weight `1` is the identity. -/
@[simp]
theorem twist_one (n : ℕ) : twist (1 : G → R) n = LinearMap.id :=
  linearMap_ext fun c ↦ by simp

variable {w}

/-- For a weight constant along paths, the twist commutes with the boundary. -/
theorem twist_boundary (hw : ∀ ⦃x y : G⦄, Joined x y → w x = w y) (n : ℕ) :
    twist w n ∘ₗ boundary G R n = boundary G R n ∘ₗ twist w (n + 1) :=
  linearMap_ext fun c ↦ by
    have hface : ∀ (i : Fin (n + 1)) (t : I), w (SingularCube.face i t c 0) = w (c 0) :=
      fun i t ↦ by
        rw [SingularCube.face_apply]
        exact SingularCube.apply_eq_apply_zero_of_joined w hw c _
    simp only [LinearMap.comp_apply, boundary_ofCube, twist_ofCube, map_smul, map_sum, map_sub,
      hface, Finset.smul_sum, smul_sub, smul_comm (w (c 0))]

end NormalizedCubicalChain

section Monoid

variable [Monoid G] [ContinuousMul G] (χ : G →* R)

namespace NormalizedCubicalChain

omit [ContinuousMul G] in
/-- The twist by a character fixes the unit. -/
theorem twist_one_chain : twist χ 0 (one G R) = one G R := by
  rw [one_def, twist_ofCube, SingularCube.point_apply, _root_.map_one, one_smul]

/-- The twist by a character is multiplicative for the Pontryagin product. -/
theorem twist_mul {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (b : NormalizedCubicalChain G R q) :
    twist χ (p + q) (mul G R p q a b) = mul G R p q (twist χ p a) (twist χ q b) := by
  have key : (mul G R p q).compr₂ (twist χ (p + q)) =
      (mul G R p q).compl₁₂ (twist χ p) (twist χ q) :=
    linearMap_ext fun c ↦ linearMap_ext fun d ↦ by
      have h0 : ((mulMap G).comp (SingularCube.crossProduct c d)) 0 = c 0 * d 0 := by
        rw [ContinuousMap.comp_apply, SingularCube.crossProduct_apply, mulMap_apply]
        rfl
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, twist_ofCube, map_smul,
        LinearMap.smul_apply, mul_ofCube, h0, _root_.map_mul, smul_smul]
      rw [mul_comm (χ (c 0))]
  exact LinearMap.congr_fun (LinearMap.congr_fun key a) b

end NormalizedCubicalChain

open NormalizedCubicalChain

variable (R) in
/-- The twist of `C^□_*(G; R)` by a character, as an algebra homomorphism, dimension by
dimension. -/
def cubicalChainTwistAlgHom (χ : G →* R) :
    normalizedCubicalChainAlgebra G R →ₐ[R] normalizedCubicalChainAlgebra G R :=
  DirectSum.toAlgebra R _ (fun n ↦ cubicalChainLof G R n ∘ₗ twist χ n)
    (by
      rw [gOne_one, LinearMap.comp_apply, twist_one_chain, DirectSum.lof_eq_of]
      rfl)
    (fun {i j} a b ↦ by
      rw [gMul_mul, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        twist_mul, cubicalChainLof_mul])

/-- The twist on a chain of dimension `n`. -/
@[simp]
theorem cubicalChainTwistAlgHom_lof (n : ℕ) (y : NormalizedCubicalChain G R n) :
    cubicalChainTwistAlgHom R χ (cubicalChainLof G R n y) =
      cubicalChainLof G R n (twist χ n y) := by
  rw [DirectSum.lof_eq_of]
  exact DirectSum.toAddMonoid_of _ _ _

/-- The twist preserves the cohomological degree. -/
theorem cubicalChainTwistAlgHom_mem {i : ℤ} {a : normalizedCubicalChainAlgebra G R}
    (ha : a ∈ cubicalChainGrading G R i) :
    cubicalChainTwistAlgHom R χ a ∈ cubicalChainGrading G R i := by
  rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨n, y, hn, rfl⟩
  · rw [map_zero]
    exact zero_mem _
  · rw [cubicalChainTwistAlgHom_lof]
    exact (mem_cubicalChainGrading_iff G R).2 (Or.inr ⟨n, _, hn, rfl⟩)

variable {χ}

/-- For a character constant along paths, the twist commutes with the differential. -/
theorem cubicalChainDifferential_cubicalChainTwistAlgHom
    (hχ : ∀ ⦃x y : G⦄, Joined x y → χ x = χ y) (a : normalizedCubicalChainAlgebra G R) :
    cubicalChainDifferential G R (cubicalChainTwistAlgHom R χ a) =
      cubicalChainTwistAlgHom R χ (cubicalChainDifferential G R a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    rw [← DirectSum.lof_eq_of R, cubicalChainTwistAlgHom_lof]
    rcases n with _ | k
    · rw [cubicalChainDifferential_lof_zero, cubicalChainDifferential_lof_zero, map_zero]
    · rw [cubicalChainDifferential_lof_succ, cubicalChainDifferential_lof_succ,
        cubicalChainTwistAlgHom_lof, ← LinearMap.comp_apply (boundary G R k),
        ← twist_boundary hχ, LinearMap.comp_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

variable (R) in
/-- **The twist by a path-constant character is a morphism of DG algebras** of `C^□_*(G; R)`:
on a cube, `σ ↦ χ (σ 0) • σ`.  For the Moore loop space this is the source's `Φ^L`. -/
def cubicalChainTwist (χ : G →* R) (hχ : ∀ ⦃x y : G⦄, Joined x y → χ x = χ y) :
    DGAlgHom (cubicalChain_isDGAlgebra G R) (cubicalChain_isDGAlgebra G R) where
  toAlgHom := cubicalChainTwistAlgHom R χ
  map_mem := cubicalChainTwistAlgHom_mem χ
  map_d' := cubicalChainDifferential_cubicalChainTwistAlgHom hχ

/-- The twist on a chain of dimension `n`. -/
@[simp]
theorem cubicalChainTwist_lof (hχ : ∀ ⦃x y : G⦄, Joined x y → χ x = χ y) (n : ℕ)
    (y : NormalizedCubicalChain G R n) :
    cubicalChainTwist R χ hχ (cubicalChainLof G R n y) = cubicalChainLof G R n (twist χ n y) :=
  cubicalChainTwistAlgHom_lof χ n y

/-- **Twisting is multiplicative in the character.** -/
theorem cubicalChainTwist_mul {ψ : G →* R} (hχ : ∀ ⦃x y : G⦄, Joined x y → χ x = χ y)
    (hψ : ∀ ⦃x y : G⦄, Joined x y → ψ x = ψ y) :
    (cubicalChainTwist R χ hχ).comp (cubicalChainTwist R ψ hψ) =
      cubicalChainTwist R (χ * ψ) fun x y h ↦ by
        rw [MonoidHom.mul_apply, MonoidHom.mul_apply, hχ h, hψ h] :=
  cubicalChain_dgAlgHom_ext fun n y ↦ by
    rw [DGAlgHom.comp_apply, cubicalChainTwist_lof, cubicalChainTwist_lof, cubicalChainTwist_lof,
      ← LinearMap.comp_apply (twist χ n), twist_comp]
    rfl

/-- The twist by the trivial character is the identity. -/
@[simp]
theorem cubicalChainTwist_one :
    cubicalChainTwist R (1 : G →* R) (fun _ _ _ ↦ rfl) =
      DGAlgHom.id (cubicalChain_isDGAlgebra G R) :=
  cubicalChain_dgAlgHom_ext fun n y ↦ by
    rw [cubicalChainTwist_lof, DGAlgHom.id_apply]
    exact congrArg _ (LinearMap.congr_fun (twist_one n) y)

end Monoid

end TauCeti

end
