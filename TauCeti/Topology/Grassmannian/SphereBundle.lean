/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Reflection
public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.FrameQuotient
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The sphere bundle `SO(n) → SO(1 + n) → Sⁿ`

Evaluating a special orthogonal matrix on the first coordinate vector `e₀` gives the map
`SO(1 + n) → Sⁿ`, `A ↦ A e₀` (`TauCeti.specialOrthogonalSphereMap`), onto the unit sphere of
`ℝ^(1 + n)`. Its fibre over `e₀` is the block subgroup `diag(1, SO(n))`, the image of
`Matrix.SpecialOrthogonalGroup.fromBlocksOne`. For `n ≥ 1` this map is a locally trivial bundle
with fibre `SO(n)`, and hence a Serre fibration.

The charts come from explicit local sections. For unit vectors `b` and `y` with `y ≠ -b`, the
reflection in `b` followed by the reflection in `b + y` is a rotation taking `b` to `y`
(`TauCeti.sphereRotation`), and it depends continuously on `y`. Composing it with a fixed rotation
taking `e₀` to `b` gives a continuous section of `A ↦ A e₀` over the complement of `-b`. Through
the identification of the sphere with the orthonormal one-frames
(`TauCeti.finiteOrthonormalFrame.sphereHomeomorph`) and the homogeneous-space description
`SO(1 + n) ⧸ Stab(e₀) ≃ₜ V₁(ℝ^(1 + n))`, such a section is a local section of a subgroup quotient,
which yields the chart (`Subgroup.localSectionTrivialization`).

The coordinates are indexed by `Fin (1 + n)`, so that the block subgroup `diag(1, SO(n))` is the
image of `fromBlocksOne ℝ 1 n` without reindexing.

## Main definitions

* `TauCeti.finiteOrthonormalFrame.sphereHomeomorph`: orthonormal one-frames are unit vectors.
* `TauCeti.specialOrthogonalSphereMap`: the evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`.
* `TauCeti.sphereRotation`: the product of two reflections taking `b` to `y`.

## Main results

* `TauCeti.specialOrthogonalSphereMap_eq_specialOrthogonalSphereMap_one_iff`: the fibre over `e₀`
  is the image of `SO(n)`.
* `TauCeti.exists_trivialization_specialOrthogonalSphereMap`: a chart with fibre `SO(n)` over the
  complement of each point.
* `TauCeti.specialOrthogonalSphereMap_mem_serreFibrations`: `SO(1 + n) → Sⁿ` is a Serre fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (fiber bundles of
  orthogonal groups over spheres).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.34, where this fibration
  produces the classes of `SO(n + 1)` covering odd spheres.
-/

public section

open Matrix Metric Set Topology

noncomputable section

namespace TauCeti

/-! ### Unit vectors as orthonormal one-frames -/

namespace finiteOrthonormalFrame

/-- An orthonormal one-frame of `ℝ^N` is the same as a unit vector of `EuclideanSpace ℝ (Fin N)`. -/
def sphereHomeomorph (N : ℕ) :
    finiteOrthonormalFrame ℝ 1 N ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin N)) 1 where
  toFun f := ⟨WithLp.toLp 2 (f.1 0), by simpa using f.2.1 0⟩
  invFun y := ⟨fun _ ↦ WithLp.ofLp (y : EuclideanSpace ℝ (Fin N)), by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j]
    simp [norm_eq_of_mem_sphere]⟩
  left_inv f := Subtype.ext <| funext fun i ↦ by rw [Subsingleton.elim i 0]
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp
    ((continuous_apply 0).comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk (continuous_pi fun _ ↦
    (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val) _

@[simp]
theorem coe_sphereHomeomorph_apply {N : ℕ} (f : finiteOrthonormalFrame ℝ 1 N) :
    (sphereHomeomorph N f : EuclideanSpace ℝ (Fin N)) = WithLp.toLp 2 (f.1 0) :=
  (rfl)

@[simp]
theorem coe_sphereHomeomorph_symm_apply {N : ℕ} (y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (i : Fin 1) :
    ((sphereHomeomorph N).symm y).1 i = WithLp.ofLp (y : EuclideanSpace ℝ (Fin N)) :=
  (rfl)

end finiteOrthonormalFrame

/-! ### Rotations taking one unit vector to another -/

section Rotation

variable {N : ℕ}

/-- The dot product of the coordinates of a Euclidean vector with themselves is its squared
norm. -/
private theorem dotProduct_ofLp_self (x : EuclideanSpace ℝ (Fin N)) :
    WithLp.ofLp x ⬝ᵥ WithLp.ofLp x = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Two unit vectors that are not antipodal have nonzero sum. -/
private theorem coe_add_coe_ne_zero {b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1} (h : y ≠ -b) :
    (b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N)) ≠ 0 := fun h0 ↦
  h (Subtype.ext (by rw [coe_neg_sphere]; exact eq_neg_of_add_eq_zero_right h0))

/-- The rotation taking a unit vector `b` to a unit vector `y ≠ -b`: the reflection in `b`
followed by the reflection in `b + y`. It is the identity when `y = -b`. -/
def sphereRotation (b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    specialOrthogonalGroup (Fin N) ℝ :=
  if h : y = -b then 1 else
    reflectionPair (WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))))
      (WithLp.ofLp (b : EuclideanSpace ℝ (Fin N)))
      (2 / (WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))) ⬝ᵥ
        WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))))) 2
      (div_mul_cancel₀ _ <| by
        rw [dotProduct_ofLp_self]
        exact pow_ne_zero 2 (norm_ne_zero_iff.2 (coe_add_coe_ne_zero h)))
      (by rw [dotProduct_ofLp_self, norm_eq_of_mem_sphere]; norm_num)

/-- The rotation taking `b` to the antipode `-b` is, by convention, the identity. -/
@[simp]
theorem sphereRotation_neg_self (b : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    sphereRotation b (-b) = 1 := by
  simp [sphereRotation]

/-- Away from the antipode of `b`, `sphereRotation b y` is the product of the reflections in
`b + y` and in `b`. -/
theorem coe_sphereRotation_of_ne {b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1} (h : y ≠ -b) :
    (sphereRotation b y : Matrix (Fin N) (Fin N) ℝ) =
      reflectionMatrix
          (WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))))
          (2 / (WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))) ⬝ᵥ
            WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))))) *
        reflectionMatrix (WithLp.ofLp (b : EuclideanSpace ℝ (Fin N))) 2 := by
  simp only [sphereRotation, h, ↓reduceDIte, coe_reflectionPair]

/-- The reflection in `u` followed by the reflection in `u + w` takes a unit vector `u` to a unit
vector `w`, provided `u + w ≠ 0`. -/
private theorem reflectionMatrix_add_mulVec_reflectionMatrix_mulVec {u w : Fin N → ℝ}
    (hu : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ w = 1) (hv : (u + w) ⬝ᵥ (u + w) ≠ 0) :
    reflectionMatrix (u + w) (2 / ((u + w) ⬝ᵥ (u + w))) *ᵥ (reflectionMatrix u 2 *ᵥ u) = w := by
  have hvv : (u + w) ⬝ᵥ (u + w) = 2 * (1 + w ⬝ᵥ u) := by
    simp only [add_dotProduct, dotProduct_add, hu, hw, dotProduct_comm u w]
    ring
  -- The first reflection sends `u` to `-u`; the second sends `-u` to `w`.
  have hdot : (u + w) ⬝ᵥ (u - ((2 : ℝ) * 1) • u) = -(1 + w ⬝ᵥ u) := by
    simp only [add_dotProduct, dotProduct_sub, dotProduct_smul, hu, smul_eq_mul]
    ring
  have hscal : 2 / ((u + w) ⬝ᵥ (u + w)) * -(1 + w ⬝ᵥ u) = -1 := by
    rw [hvv] at hv ⊢
    have h1 : 1 + w ⬝ᵥ u ≠ 0 := fun h0 ↦ hv (by rw [h0, mul_zero])
    field_simp
  rw [reflectionMatrix_mulVec, reflectionMatrix_mulVec, hu, hdot, hscal]
  module

/-- The rotation `sphereRotation b y` takes `b` to `y` when `y ≠ -b`. -/
theorem sphereRotation_mulVec {b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1} (h : y ≠ -b) :
    (sphereRotation b y : Matrix (Fin N) (Fin N) ℝ) *ᵥ WithLp.ofLp (b : EuclideanSpace ℝ (Fin N)) =
      WithLp.ofLp (y : EuclideanSpace ℝ (Fin N)) := by
  have hunit (x : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
      WithLp.ofLp (x : EuclideanSpace ℝ (Fin N)) ⬝ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin N)) =
        1 := by
    rw [dotProduct_ofLp_self, norm_eq_of_mem_sphere, one_pow]
  have hv : WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))) ⬝ᵥ
      WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))) ≠ 0 := by
    rw [dotProduct_ofLp_self]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (coe_add_coe_ne_zero h))
  rw [coe_sphereRotation_of_ne h, ← mulVec_mulVec]
  rw [WithLp.ofLp_add] at hv ⊢
  exact reflectionMatrix_add_mulVec_reflectionMatrix_mulVec (hunit b) (hunit y) hv

/-- The rotation `sphereRotation b y` depends continuously on `y` away from `-b`. -/
theorem continuousOn_sphereRotation (b : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    ContinuousOn (sphereRotation b) {-b}ᶜ := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hv : Continuous fun y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 ↦
      WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))) := by fun_prop
  have hR : ContinuousOn (fun y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 ↦
      reflectionMatrix
        (WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))))
        (2 / (WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))) ⬝ᵥ
          WithLp.ofLp ((b : EuclideanSpace ℝ (Fin N)) + (y : EuclideanSpace ℝ (Fin N))))))
      {-b}ᶜ :=
    TauCeti.Matrix.continuousOn_reflectionMatrix.comp hv.continuousOn fun y hy h0 ↦
      coe_add_coe_ne_zero hy (by simpa using congrArg (WithLp.toLp 2) h0)
  have hM := (continuous_id.matrix_mul (continuous_const
    (y := reflectionMatrix (WithLp.ofLp (b : EuclideanSpace ℝ (Fin N))) 2))).comp_continuousOn hR
  exact hM.congr fun y hy ↦ coe_sphereRotation_of_ne hy

end Rotation

/-! ### The evaluation map `SO(1 + n) → Sⁿ` -/

variable (n : ℕ)

/-- The evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`, on the first coordinate vector `e₀`. -/
def specialOrthogonalSphereMap (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1 :=
  finiteOrthonormalFrame.sphereHomeomorph (1 + n)
    (finiteOrthonormalFrame.unitaryMap ⟨A.1, A.2.1⟩
      (finiteOrthonormalFrame.standard ℝ (Nat.le_add_right 1 n)))

variable {n}

/-- In coordinates, `specialOrthogonalSphereMap n A` is the first column `A e₀` of `A`. -/
@[simp]
theorem coe_specialOrthogonalSphereMap (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    (specialOrthogonalSphereMap n A : EuclideanSpace ℝ (Fin (1 + n))) =
      WithLp.toLp 2 ((A : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ).col 0) := by
  simp [specialOrthogonalSphereMap,
    show Fin.castLE (Nat.le_add_right 1 n) (0 : Fin 1) = 0 from Fin.ext (by simp)]

variable (n) in
/-- The evaluation map `SO(1 + n) → Sⁿ` is continuous. -/
theorem continuous_specialOrthogonalSphereMap : Continuous (specialOrthogonalSphereMap n) :=
  (finiteOrthonormalFrame.sphereHomeomorph (1 + n)).continuous.comp
    (finiteOrthonormalFrame.continuous_unitaryMap.comp
      ((continuous_subtype_val.subtype_mk _).prodMk continuous_const))

/-- The evaluation map is equivariant: `(A B) e₀ = A (B e₀)`. -/
theorem ofLp_specialOrthogonalSphereMap_mul (A B : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    WithLp.ofLp (specialOrthogonalSphereMap n (A * B) : EuclideanSpace ℝ (Fin (1 + n))) =
      (A : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ) *ᵥ
        WithLp.ofLp (specialOrthogonalSphereMap n B : EuclideanSpace ℝ (Fin (1 + n))) := by
  rw [coe_specialOrthogonalSphereMap, coe_specialOrthogonalSphereMap, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, ← mulVec_single_one, ← mulVec_single_one, Submonoid.coe_mul,
    mulVec_mulVec]

/-- The fibre of `A ↦ A e₀` over `e₀` is the block subgroup `diag(1, SO(n))`. -/
theorem specialOrthogonalSphereMap_eq_specialOrthogonalSphereMap_one_iff
    {A : specialOrthogonalGroup (Fin (1 + n)) ℝ} :
    specialOrthogonalSphereMap n A = specialOrthogonalSphereMap n 1 ↔
      A ∈ (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n).range := by
  rw [SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff, Fin.forall_fin_one, Subtype.ext_iff,
    coe_specialOrthogonalSphereMap, coe_specialOrthogonalSphereMap,
    (WithLp.toLp_injective 2).eq_iff, OneMemClass.coe_one, ← mulVec_single_one,
    ← mulVec_single_one, one_mulVec, show Fin.castAdd n (0 : Fin 1) = 0 from Fin.ext (by simp)]

/-- For `n ≥ 1`, every unit vector of `ℝ^(1 + n)` is `A e₀` for some `A ∈ SO(1 + n)`. -/
theorem surjective_specialOrthogonalSphereMap [NeZero n] :
    Function.Surjective (specialOrthogonalSphereMap n) :=
  (finiteOrthonormalFrame.sphereHomeomorph (1 + n)).surjective.comp
    (finiteOrthonormalFrame.specialOrthogonal_unitaryMap_standard_surjective
      (Nat.lt_add_of_pos_right (Nat.pos_of_neZero n)))

/-! ### Local triviality -/

/-- For `n ≥ 1` and each unit vector `b`, the evaluation map `SO(1 + n) → Sⁿ` has a chart with
fibre `SO(n)` over the complement of `-b`. -/
theorem exists_trivialization_specialOrthogonalSphereMap [NeZero n]
    (b : sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1) :
    ∃ e : Bundle.Trivialization (specialOrthogonalGroup (Fin n) ℝ) (specialOrthogonalSphereMap n),
      e.baseSet = {-b}ᶜ := by
  have hn : 1 < 1 + n := Nat.lt_add_of_pos_right (Nat.pos_of_neZero n)
  let H := finiteOrthonormalFrame.specialOrthogonalStabilizer (r := 1) hn.le
  -- The sphere is the homogeneous space `SO(1 + n) ⧸ H`.
  let φ : specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1 :=
    (finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph hn).trans
      (finiteOrthonormalFrame.sphereHomeomorph (1 + n))
  have hφ (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
      φ (QuotientGroup.mk A) = specialOrthogonalSphereMap n A := by
    exact congrArg (finiteOrthonormalFrame.sphereHomeomorph (1 + n))
      (finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph_mk hn A)
  -- A rotation `g` taking `e₀` to `b`, followed by rotations taking `b` to nearby points.
  obtain ⟨g, hg⟩ := surjective_specialOrthogonalSphereMap (n := n) b
  let U : Set (specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H) :=
    φ ⁻¹' {-b}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton.preimage φ.continuous
  let s : specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H → specialOrthogonalGroup (Fin (1 + n)) ℝ :=
    fun q ↦ sphereRotation b (φ q) * g
  have hs : ContinuousOn s U :=
    ((continuousOn_sphereRotation b).comp φ.continuous.continuousOn fun _ hq ↦ hq).mul
      continuousOn_const
  have hsec : ∀ q ∈ U, (s q : specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H) = q := by
    intro q hq
    apply φ.injective
    rw [hφ]
    apply Subtype.ext
    apply WithLp.ofLp_injective
    rw [ofLp_specialOrthogonalSphereMap_mul, hg]
    exact sphereRotation_mulVec hq
  let e := Subgroup.localSectionTrivialization H U hU s hs hsec
  let e' := (e.homeomorphComp φ).transFiberHomeomorph
    (finiteOrthonormalFrame.specialOrthogonalStabilizerHomeomorph 1 n).symm
  have hproj : φ ∘ (QuotientGroup.mk : specialOrthogonalGroup (Fin (1 + n)) ℝ → _) =
      specialOrthogonalSphereMap n := funext hφ
  rw [← hproj]
  refine ⟨e', ?_⟩
  simp only [e', Bundle.Trivialization.transFiberHomeomorph, Bundle.Trivialization.homeomorphComp,
    e, Subgroup.localSectionTrivialization_baseSet, U]
  ext y
  simp only [Set.mem_preimage, Homeomorph.apply_symm_apply]

/-- For `n ≥ 1`, the evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`, is a Serre fibration: it is
locally trivial with fibre `SO(n)`. -/
theorem specialOrthogonalSphereMap_mem_serreFibrations [NeZero n] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialOrthogonalSphereMap n,
          continuous_specialOrthogonalSphereMap n⟩ :
        _root_.TopCat.of (specialOrthogonalGroup (Fin (1 + n)) ℝ) ⟶
          _root_.TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)) := by
  refine TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialOrthogonalGroup (Fin n) ℝ) fun b ↦ ?_
  obtain ⟨e, he⟩ := exists_trivialization_specialOrthogonalSphereMap (n := n) b
  refine ⟨e, ?_⟩
  rw [he]
  exact ne_neg_of_mem_unit_sphere ℝ b

end TauCeti
