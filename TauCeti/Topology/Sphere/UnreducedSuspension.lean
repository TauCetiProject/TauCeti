/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Lp.ProdLp.Sphere
public import TauCeti.Analysis.Normed.Module.Normalize
public import TauCeti.Topology.Constructions.UnreducedSuspension

/-!
# The unreduced suspension of a sphere is a sphere

For a real normed space `E`, the map `[x, t] ↦ (2 √(t (1 - t)) • x, 1 - 2 t)` sends the unreduced
suspension of the unit sphere of `E` into the unit sphere of the `L²` product `WithLp 2 (E × ℝ)`,
since `4 t (1 - t) + (1 - 2 t)² = 1`. The end `t = 0` goes to the pole `(0, 1)` and the end
`t = 1` to the pole `(0, -1)`. The map is always injective, and surjective when the sphere of `E`
is nonempty, that is when `E` is nontrivial. When `E` is finite dimensional the suspension is
compact and the sphere is Hausdorff, so this bijection is a homeomorphism. For Euclidean spheres
this is `SSⁿ ≅ Sⁿ⁺¹`, with the suspension coordinate last.

The coordinates are chosen to match `TauCeti.sphereJoinHomeomorph`: a point of the join of two
spheres with join coordinate `t` has squared norms `1 - t` and `t` in its two components, and the
Hopf construction keeps `t`, so the last coordinate `1 - 2 t` of its image is the difference of
these squared norms (`TauCeti.coe_sphereHopfMap`).

## Main declarations

* `TauCeti.sphereUnreducedSuspensionMap`: the continuous map
  `UnreducedSuspension (sphere (0 : E) 1) → sphere (0 : WithLp 2 (E × ℝ)) 1`.
* `TauCeti.sphereUnreducedSuspensionMap_injective`,
  `TauCeti.sphereUnreducedSuspensionMap_surjective`: it is bijective.
* `TauCeti.sphereUnreducedSuspensionHomeomorph`: for finite-dimensional `E`, the homeomorphism of
  the unreduced suspension of the unit sphere with the unit sphere of `WithLp 2 (E × ℝ)`; its
  inverse is given by `TauCeti.sphereUnreducedSuspensionHomeomorph_symm_apply`.
* `TauCeti.euclideanSphereUnreducedSuspensionHomeomorph`: the homeomorphism `SSⁿ ≃ₜ Sⁿ⁺¹` of unit
  spheres in Euclidean spaces.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, *Operations on Spaces*, the suspension `SX` and `SSⁿ = Sⁿ⁺¹`.
-/

public section

noncomputable section

namespace TauCeti

open Metric unitInterval WithLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The squared norms `4 t (1 - t)` and `(1 - 2 t)²` of the two components of the image of
`[x, t]` add up to `1`. -/
private lemma two_mul_sqrt_mul_one_sub_sq_add_sq (t : I) :
    (2 * √((t : ℝ) * (1 - t))) ^ 2 + (1 - 2 * (t : ℝ)) ^ 2 = 1 := by
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (nonneg t) (sub_nonneg.2 (le_one t)))]
  ring

/-- The map `(x, t) ↦ (2 √(t (1 - t)) • x, 1 - 2 t)` from `Sᴱ × I` to the unit sphere of the `L²`
product, before passing to the unreduced suspension. -/
private def sphereUnreducedSuspensionMapAux :
    C(sphere (0 : E) 1 × I, sphere (0 : WithLp 2 (E × ℝ)) 1) where
  toFun p := ⟨toLp 2 ((2 * √((p.2 : ℝ) * (1 - p.2))) • (p.1 : E), 1 - 2 * (p.2 : ℝ)), by
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      prod_norm_sq_eq_of_L2]
    simp only [toLp_fst, toLp_snd, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one,
      sq_abs]
    exact two_mul_sqrt_mul_one_sub_sq_add_sq p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((prod_continuous_toLp 2 E ℝ).comp ?_) _
    fun_prop

/-- The map `[x, t] ↦ (2 √(t (1 - t)) • x, 1 - 2 t)` from the unreduced suspension of the unit
sphere of `E` to the unit sphere of `WithLp 2 (E × ℝ)`. It is a homeomorphism when `E` is
nontrivial and finite dimensional (`TauCeti.sphereUnreducedSuspensionHomeomorph`). -/
def sphereUnreducedSuspensionMap :
    C(UnreducedSuspension (sphere (0 : E) 1), sphere (0 : WithLp 2 (E × ℝ)) 1) :=
  UnreducedSuspension.lift sphereUnreducedSuspensionMapAux
    (fun x x' => Subtype.ext <| by simp [sphereUnreducedSuspensionMapAux])
    (fun x x' => Subtype.ext <| by simp [sphereUnreducedSuspensionMapAux])

@[simp]
theorem coe_sphereUnreducedSuspensionMap_mk (x : sphere (0 : E) 1) (t : I) :
    (sphereUnreducedSuspensionMap (UnreducedSuspension.mk _ (x, t)) : WithLp 2 (E × ℝ)) =
      toLp 2 ((2 * √((t : ℝ) * (1 - t))) • (x : E), 1 - 2 * (t : ℝ)) := by
  simp [sphereUnreducedSuspensionMap, sphereUnreducedSuspensionMapAux]

/-- The map from the unreduced suspension of a sphere to the sphere of the `L²` product with `ℝ`
is injective. -/
theorem sphereUnreducedSuspensionMap_injective :
    Function.Injective (sphereUnreducedSuspensionMap (E := E)) := by
  intro a b hab
  induction a using UnreducedSuspension.induction with | h p => ?_
  induction b using UnreducedSuspension.induction with | h q => ?_
  obtain ⟨x, s⟩ := p
  obtain ⟨x', t⟩ := q
  have h := congrArg (fun z : sphere (0 : WithLp 2 (E × ℝ)) 1 => ofLp (z : WithLp 2 (E × ℝ))) hab
  simp only [coe_sphereUnreducedSuspensionMap_mk, ofLp_toLp, Prod.mk.injEq] at h
  obtain ⟨hx, ht⟩ := h
  obtain rfl : s = t := Subtype.ext (by linarith)
  refine UnreducedSuspension.mk_eq_mk_iff.2 ⟨rfl, fun hs₀ hs₁ => Subtype.ext ?_⟩
  refine smul_right_injective E (mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.2 ?_)) hx
  exact mul_pos (lt_of_le_of_ne (nonneg s) fun h => hs₀ (Subtype.ext h.symm))
    (sub_pos.2 (lt_of_le_of_ne (le_one s) fun h => hs₁ (Subtype.ext h)))

omit [NormedSpace ℝ E] in
/-- The suspension coordinate `(1 - c) / 2` of a unit vector `(a, c)` of the `L²` product with `ℝ`
lies in the unit interval. -/
theorem one_sub_snd_div_two_mem_unitInterval (p : sphere (0 : WithLp 2 (E × ℝ)) 1) :
    (1 - (p : WithLp 2 (E × ℝ)).snd) / 2 ∈ I := by
  have hn := sq_norm_fst_add_sq_norm_snd_eq_one p
  rw [Real.norm_eq_abs, sq_abs] at hn
  exact ⟨by nlinarith [sq_nonneg ‖(p : WithLp 2 (E × ℝ)).fst‖,
      sq_nonneg ((p : WithLp 2 (E × ℝ)).snd + 1)],
    by nlinarith [sq_nonneg ‖(p : WithLp 2 (E × ℝ)).fst‖,
      sq_nonneg ((p : WithLp 2 (E × ℝ)).snd - 1)]⟩

/-- A unit vector `(a, c)` of the `L²` product with `ℝ` is the image of the point
`[a / ‖a‖, (1 - c) / 2]` of the unreduced suspension, where the direction of `a` is
`TauCeti.sphereDirection` with any fallback unit vector `e`. -/
theorem sphereUnreducedSuspensionMap_mk_sphereDirection (e : sphere (0 : E) 1)
    (p : sphere (0 : WithLp 2 (E × ℝ)) 1) :
    sphereUnreducedSuspensionMap (UnreducedSuspension.mk _
      (sphereDirection e (p : WithLp 2 (E × ℝ)).fst,
        ⟨_, one_sub_snd_div_two_mem_unitInterval p⟩)) = p := by
  obtain ⟨p, hp⟩ := p
  have hn := sq_norm_fst_add_sq_norm_snd_eq_one ⟨p, hp⟩
  rw [Real.norm_eq_abs, sq_abs] at hn
  ext1
  rw [coe_sphereUnreducedSuspensionMap_mk]
  have h2 : 2 * √((1 - p.snd) / 2 * (1 - (1 - p.snd) / 2)) = ‖p.fst‖ := by
    rw [show (1 - p.snd) / 2 * (1 - (1 - p.snd) / 2) = (‖p.fst‖ / 2) ^ 2 by
      linear_combination (-1 / 4 : ℝ) * hn, Real.sqrt_sq (by positivity)]
    ring
  simp only [h2, norm_smul_sphereDirection, show 1 - 2 * ((1 - p.snd) / 2) = p.snd by ring]
  -- `toLp 2 (p.fst, p.snd) = p` is the eta law of the product and of `WithLp`.
  rfl

/-- The map from the unreduced suspension of the unit sphere of a nontrivial space to the sphere
of the `L²` product with `ℝ` is surjective. -/
theorem sphereUnreducedSuspensionMap_surjective [Nontrivial E] :
    Function.Surjective (sphereUnreducedSuspensionMap (E := E)) := by
  obtain ⟨e⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one |>.coe_sort
  exact fun p => ⟨_, sphereUnreducedSuspensionMap_mk_sphereDirection e p⟩

theorem sphereUnreducedSuspensionMap_bijective [Nontrivial E] :
    Function.Bijective (sphereUnreducedSuspensionMap (E := E)) :=
  ⟨sphereUnreducedSuspensionMap_injective, sphereUnreducedSuspensionMap_surjective⟩

variable [Nontrivial E] [FiniteDimensional ℝ E]

variable (E) in
/-- **The unreduced suspension of a sphere is a sphere.** For a nontrivial finite-dimensional real
normed space `E`, the map `[x, t] ↦ (2 √(t (1 - t)) • x, 1 - 2 t)` is a homeomorphism from the
unreduced suspension of the unit sphere of `E` to the unit sphere of `WithLp 2 (E × ℝ)`. -/
def sphereUnreducedSuspensionHomeomorph :
    UnreducedSuspension (sphere (0 : E) 1) ≃ₜ sphere (0 : WithLp 2 (E × ℝ)) 1 :=
  sphereUnreducedSuspensionMap.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ sphereUnreducedSuspensionMap_bijective)

@[simp]
theorem coe_sphereUnreducedSuspensionHomeomorph :
    ⇑(sphereUnreducedSuspensionHomeomorph E) = sphereUnreducedSuspensionMap := (rfl)

@[simp]
theorem sphereUnreducedSuspensionHomeomorph_symm_sphereUnreducedSuspensionMap
    (z : UnreducedSuspension (sphere (0 : E) 1)) :
    (sphereUnreducedSuspensionHomeomorph E).symm (sphereUnreducedSuspensionMap z) = z :=
  (sphereUnreducedSuspensionHomeomorph E).symm_apply_apply z

/-- The inverse of `TauCeti.sphereUnreducedSuspensionHomeomorph` sends a unit vector `(a, c)` to
the point `[a / ‖a‖, (1 - c) / 2]` of the unreduced suspension, where the direction of `a` is
`TauCeti.sphereDirection` with any fallback unit vector `e`. -/
theorem sphereUnreducedSuspensionHomeomorph_symm_apply (e : sphere (0 : E) 1)
    (p : sphere (0 : WithLp 2 (E × ℝ)) 1) :
    (sphereUnreducedSuspensionHomeomorph E).symm p =
      UnreducedSuspension.mk _ (sphereDirection e (p : WithLp 2 (E × ℝ)).fst,
        ⟨_, one_sub_snd_div_two_mem_unitInterval p⟩) :=
  (sphereUnreducedSuspensionHomeomorph E).symm_apply_eq.2
    (sphereUnreducedSuspensionMap_mk_sphereDirection e p).symm

/-- **The unreduced suspension `SSⁿ` is `Sⁿ⁺¹`.** The homeomorphism sends `[x, t]` to the unit
vector of `ℝⁿ⁺²` whose first `n + 1` coordinates are those of `2 √(t (1 - t)) • x` and whose last
coordinate is `1 - 2 t`. -/
def euclideanSphereUnreducedSuspensionHomeomorph (n : ℕ) :
    UnreducedSuspension (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1 :=
  -- Identify the `L²` product of `ℝⁿ⁺¹` and `ℝ` isometrically with `ℝⁿ⁺²`, the factor `ℝ` giving
  -- the last coordinate, and restrict this identification to the unit spheres.
  (sphereUnreducedSuspensionHomeomorph _).trans <|
    ((LinearIsometryEquiv.withLpProdCongr 2 (.refl ℝ _)
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr).trans
      ((PiLp.sumPiLpEquivProdLpPiLp 2 fun _ => ℝ).symm.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv))).toHomeomorph.subtype
      fun z => by simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph,
        LinearIsometryEquiv.norm_map]

/-- The first `n + 1` coordinates of the image of `[x, t]` in `Sⁿ⁺¹` are those of
`2 √(t (1 - t)) • x`. -/
@[simp]
theorem euclideanSphereUnreducedSuspensionHomeomorph_apply_castSucc (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (t : I) (i : Fin (n + 1)) :
    (euclideanSphereUnreducedSuspensionHomeomorph n (UnreducedSuspension.mk _ (x, t)) :
        EuclideanSpace ℝ (Fin (n + 1 + 1))) (Fin.castSucc i) =
      2 * √((t : ℝ) * (1 - t)) * (x : EuclideanSpace ℝ (Fin (n + 1))) i := by
  simp [euclideanSphereUnreducedSuspensionHomeomorph]

/-- The last coordinate of the image of `[x, t]` in `Sⁿ⁺¹` is `1 - 2 t`. -/
@[simp]
theorem euclideanSphereUnreducedSuspensionHomeomorph_apply_last (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (t : I) :
    (euclideanSphereUnreducedSuspensionHomeomorph n (UnreducedSuspension.mk _ (x, t)) :
        EuclideanSpace ℝ (Fin (n + 1 + 1))) (Fin.last (n + 1)) =
      1 - 2 * (t : ℝ) := by
  simp [euclideanSphereUnreducedSuspensionHomeomorph]

end TauCeti
