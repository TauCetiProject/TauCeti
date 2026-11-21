/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.LocalDegree
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.LoopSpace
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Sphere.Stiefel.MeridianProduct
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
import TauCeti.Analysis.SpecialFunctions.Trigonometric.UnitInterval

/-!
# The meridian loops generate the homology of the loop space of a sphere

Let `p` be a point of the unit sphere `Sⁿ` of a real inner product space `E`, `n ≥ 2`, and fix a
unit vector `u₀ ⊥ p`. Each unit vector `w ⊥ p` gives the loop `λ(w) = γ_w · γ_{u₀}⁻¹` at `p`
(`TauCeti.meridianLoopFixedReturn p u₀ w`): along the meridian `γ_w` in the direction `w` to `-p`,
and back along the meridian `γ_{u₀}`. The family `λ : S(p^⊥) → Ω_p Sⁿ` of these loops,
parametrized by the unit sphere `S(p^⊥) ≅ Sⁿ⁻¹` of the tangent space at `p`, induces an
isomorphism

`λ_* : Hₙ₋₁(S(p^⊥); ℤ) ≅ Hₙ₋₁(Ω_p Sⁿ; ℤ)`

(`TauCeti.isIso_singularHomologyFunctor_map_meridianLoopFixedReturn`). So the class
`x = λ_*[Sⁿ⁻¹]` generates `Hₙ₋₁(Ω_p Sⁿ; ℤ) ≅ ℤ`. In the proof of Proposition 6.17 of
Barraud–Damian–Humilière–Oancea this class is the degree `n - 1` generator of the Pontryagin ring
`H_*(Ω_p Sⁿ)`, there obtained from Morse homology with DG coefficients of the height function;
here it is identified directly.

## Proof

The family `λ` sends the base point `u₀` to `γ_{u₀} · γ_{u₀}⁻¹`, not to the constant loop, so its
Hurewicz classes are read after transporting along the path of loops `χ_{u₀}⁻¹`
(`TauCeti.meridianContraction`) to the constant loop; transport does not change Hurewicz classes
(`HomotopyGroup.hurewicz_homotopyGroupTransport`).

* A generalized loop `c` of `S(p^⊥)` at `u₀` that is a homeomorphism off the boundary of its cube
  (`TauCeti.exists_genLoop_sphere`) has a Hurewicz class generating `Hₙ₋₁(S(p^⊥); ℤ)`.
* Read through `λ`, transported to the constant loop and shifted from `Ω_p Sⁿ` to `Sⁿ`, it becomes
  a cube of `Sⁿ`. Off the meridian `γ_{u₀}`, this cube is the meridian `γ_{c(y)}` at twice the time,
  for `y` in the half-size inner cube: the transport collar and the return halves of the loops all
  run along `γ_{u₀}`. Every point off `γ_{u₀}` lies on exactly one meridian, at one time
  (`TauCeti.eq_and_eq_of_sphereMeridian_eq`, `TauCeti.exists_sphereMeridian_eq`), so the cube
  covers the open complement of `γ_{u₀}` exactly once, and its Hurewicz class generates
  `Hₙ(Sⁿ; ℤ)` (`GenLoop.isIso_hurewicz_of_bijOn_toSphere`).
* By the Hurewicz theorem for `Sⁿ`, the Hurewicz criterion for the `(n - 2)`-connected loop space
  `Ω_p Sⁿ`, and the loop-space shift `πₙ₋₁(Ω_p Sⁿ) ≅ πₙ(Sⁿ)`
  (`HomotopyGroup.isIso_hurewicz_genLoopLoopHomeomorph_iff`), the transported class generates
  `Hₙ₋₁(Ω_p Sⁿ; ℤ)`, so `λ_*` carries a generator to a generator.

## Main results

* `TauCeti.isIso_singularHomologyFunctor_map_meridianLoopFixedReturn`: for `n ≥ 2`, the meridian
  loops `w ↦ γ_w · γ_{u₀}⁻¹` induce an isomorphism `Hₙ₋₁(S(p^⊥); ℤ) ≅ Hₙ₋₁(Ω_p Sⁿ; ℤ)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, proofs of Propositions 6.17 and
  6.18.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1 (change of base point) and Section 4.2 (the Hurewicz theorem).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Module Real Set
open scoped RealInnerProductSpace unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-! ### The cube of the transported meridian loops -/

section Meridian

variable {k : ℕ} (u₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
  (c : Ω^ (Fin k) (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) u₀)

/-- The cube of the sphere attached to a generalized loop `c` of `S(p^⊥)` at `u₀`: read through
the meridian loops `w ↦ γ_w · γ_{u₀}⁻¹`, transported to the constant loop along `χ_{u₀}⁻¹`, and
shifted from the loop space to the sphere. -/
private def meridianCube : Ω^ (Fin (k + 1)) (sphere (0 : E) 1) p :=
  GenLoop.genLoopLoopHomeomorph p k (GenLoop.transport (meridianContraction p u₀).symm
    (GenLoop.map (meridianLoopFixedReturn p u₀) (meridianLoopFixedReturn_apply p u₀ u₀) c))

/-- The cube of the transported meridian loops: on the half-size cube in the first `k`
coordinates it reads the loops `γ_w · γ_{u₀}⁻¹` along `c`, and outside it runs the path of loops
`χ_{u₀}⁻¹`. -/
private theorem meridianCube_apply (z : I^(Fin (k + 1))) :
    meridianCube p u₀ c z =
      if cubeRadius (fun i : Fin k ↦ z i.castSucc) ≤ 1 / 2 then
        meridianLoop p (u₀, c (cubeScale 2 fun i : Fin k ↦ z i.castSucc)) (z (Fin.last k))
      else (meridianContraction p u₀).symm (projIcc (0 : ℝ) 1 zero_le_one
        (2 - 1 / max (cubeRadius fun i : Fin k ↦ z i.castSucc) (1 / 2))) (z (Fin.last k)) := by
  rw [meridianCube, GenLoop.genLoopLoopHomeomorph_apply, GenLoop.transport_apply_eq]
  split_ifs
  · rw [GenLoop.map_apply, meridianLoopFixedReturn_apply]
  · rfl

/-- Off the meridian `γ_{u₀}`, the cube of the transported meridian loops is on the first half of
a loop `γ_w · γ_{u₀}⁻¹`, so it is the meridian `γ_w` at twice the last coordinate. -/
private theorem meridianCube_eq_sphereMeridian {z : I^(Fin (k + 1))}
    (hz : meridianCube p u₀ c z ∉ range (sphereMeridian p u₀)) :
    cubeRadius (fun i : Fin k ↦ z i.castSucc) ≤ 1 / 2 ∧ ∃ ht : (z (Fin.last k) : ℝ) ≤ 1 / 2,
      meridianCube p u₀ c z = sphereMeridian p (c (cubeScale 2 fun i : Fin k ↦ z i.castSucc))
        ⟨2 * z (Fin.last k), by
          constructor <;> nlinarith [(z (Fin.last k)).property.1]⟩ := by
  rw [meridianCube_apply] at hz ⊢
  split_ifs at hz ⊢ with hr
  · refine ⟨hr, ?_⟩
    rw [meridianLoop_def, Path.trans_apply] at hz ⊢
    split_ifs at hz ⊢ with ht
    · exact ⟨ht, rfl⟩
    · exact absurd ⟨_, (Path.symm_apply _ _).symm⟩ hz
  · exact absurd (meridianContraction_apply_mem_range p u₀ _ _) hz

/-- **The cube of the transported meridian loops covers the complement of `γ_{u₀}` once**, when
`c` covers `S(p^⊥)` off `u₀` and identifies only points of the boundary of its cube. -/
private theorem bijOn_toSphere_meridianCube (hcs : ∀ q, q ≠ u₀ → ∃ y, c y = q)
    (hci : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k)) :
    BijOn (GenLoop.toSphere (meridianCube p u₀ c))
      (GenLoop.toSphere (meridianCube p u₀ c) ⁻¹' (range (sphereMeridian p u₀))ᶜ)
      (range (sphereMeridian p u₀))ᶜ := by
  have hpole {q : sphere (0 : E) 1} (hq : q ∉ range (sphereMeridian p u₀)) : q ≠ p ∧ q ≠ -p :=
    ⟨fun h ↦ hq ⟨0, by rw [h, Path.source]⟩, fun h ↦ hq ⟨1, by rw [h, Path.target]⟩⟩
  -- A point of the cube off `γ_{u₀}` lies on the meridian of a direction `w ≠ u₀`.
  have hne {w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {t : I}
      (hq : sphereMeridian p w t ∉ range (sphereMeridian p u₀)) : w ≠ u₀ :=
    fun h ↦ hq ⟨t, by rw [h]⟩
  have hint {y : I^(Fin k)} (hy : c y ≠ u₀) : y ∉ Cube.boundary (Fin k) :=
    fun hb ↦ hy (GenLoop.boundary c y hb)
  refine ⟨fun _ h ↦ h, fun s hs s' hs' h ↦ ?_, fun q hq ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := cubeToSphere_surjective _ s
    obtain ⟨z', rfl⟩ := cubeToSphere_surjective _ s'
    simp only [mem_preimage, GenLoop.toSphere_cubeToSphere] at hs hs' h
    obtain ⟨hr, ht, hz⟩ := meridianCube_eq_sphereMeridian p u₀ c hs
    obtain ⟨hr', ht', hz'⟩ := meridianCube_eq_sphereMeridian p u₀ c hs'
    rw [hz] at hs
    rw [hz, hz'] at h
    obtain ⟨hw, htt⟩ := eq_and_eq_of_sphereMeridian_eq p h (hpole hs).1 (hpole hs).2
    have hc := hne hs
    rcases hci _ _ hw with hy | ⟨hb, -⟩
    · have hinit := cubeScale_injOn two_pos (show 2 * _ ≤ (1 : ℝ) by linarith)
        (show 2 * _ ≤ (1 : ℝ) by linarith) hy
      have hlast : z (Fin.last k) = z' (Fin.last k) :=
        Subtype.ext (by linarith [congrArg Subtype.val htt])
      congr 1
      funext i
      induction i using Fin.lastCases with
      | last => exact hlast
      | cast j => exact congrFun hinit j
    · exact absurd hb (hint hc)
  · obtain ⟨w, t, rfl⟩ := exists_sphereMeridian_eq p (hpole hq).1 (hpole hq).2
    obtain ⟨y, hy⟩ := hcs w (hne hq)
    obtain ⟨z₀, hr, rfl⟩ := exists_cubeScale_eq one_le_two y
    replace hr : cubeRadius z₀ ≤ 1 / 2 := by linarith
    let t' : I := ⟨t / 2, by linarith [t.property.1], by linarith [t.property.2]⟩
    have hval : meridianCube p u₀ c (Fin.snoc z₀ t') = sphereMeridian p w t := by
      rw [meridianCube_apply]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hr, ↓reduceIte, hy, meridianLoop_def,
        Path.trans_apply, t', show (t : ℝ) / 2 ≤ 1 / 2 by linarith [t.property.2], ↓reduceDIte]
      congr 1
      exact Subtype.ext (by simp only; ring)
    exact ⟨cubeToSphere _ (Fin.snoc z₀ t'),
      by rw [mem_preimage, GenLoop.toSphere_cubeToSphere, hval]; exact hq,
      by rw [GenLoop.toSphere_cubeToSphere, hval]⟩

end Meridian

/-- The cube of the transported meridian loops has a Hurewicz class generating `Hₙ(Sⁿ; ℤ)`, when
`c` covers `S(p^⊥)` off `u₀` and identifies only points of the boundary of its cube: it covers the
nonempty open complement of the meridian `γ_{u₀}` once. -/
private theorem isIso_hurewicz_meridianCube {m : ℕ} (hE : finrank ℝ E = m + 3)
    (u₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (c : Ω^ (Fin (m + 1)) (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) u₀)
    (hcs : ∀ q, q ≠ u₀ → ∃ y, c y = q)
    (hci : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin (m + 1)) ∧
      z ∈ Cube.boundary (Fin (m + 1))) :
    IsIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (meridianCube p u₀ c)) := by
  have hM : IsOpen (range (sphereMeridian p u₀))ᶜ :=
    (isCompact_range (sphereMeridian p u₀).continuous).isClosed.isOpen_compl
  have hMne : (range (sphereMeridian p u₀))ᶜ.Nonempty := by
    refine ⟨-(sphereMeridian p u₀ ⟨1 / 2, by norm_num, by norm_num⟩), fun ⟨t, ht⟩ ↦ ?_⟩
    have hu : ⟪(p : E), ((u₀ : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (u₀ : (ℝ ∙ (p : E))ᗮ).property
    have h := congrArg (fun q : sphere (0 : E) 1 ↦ ⟪(q : E), ((u₀ : (ℝ ∙ (p : E))ᗮ) : E)⟫) ht
    have hn : ‖((u₀ : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := by
      rw [Submodule.norm_coe, norm_eq_of_mem_sphere u₀]
    simp only [coe_neg_sphere, coe_sphereMeridian, inner_neg_left, inner_add_left,
      real_inner_smul_left, hu, real_inner_self_eq_norm_sq, hn, mul_one_div, sin_pi_div_two] at h
    nlinarith [sin_pi_mul_nonneg t]
  exact GenLoop.isIso_hurewicz_of_bijOn_toSphere (n := m) hE (meridianCube p u₀ c) hM hMne
    (bijOn_toSphere_meridianCube p u₀ c hcs hci)

/-! ### The class of the meridian loops -/

/-- **The meridian loops generate the homology of the loop space of a sphere.** Let `E` have
dimension `m + 3`, so that its unit sphere is `Sⁿ` with `n = m + 2 ≥ 2`, and let `p` be a point of
`Sⁿ`. For a fixed unit vector `u₀ ⊥ p`, the family of loops at `p`

`λ : S(p^⊥) → Ω_p Sⁿ`, `w ↦ γ_w · γ_{u₀}⁻¹`,

which runs to `-p` along the meridian in the direction `w` and back along the meridian in the
direction `u₀` (`TauCeti.meridianLoopFixedReturn`), induces an isomorphism
`λ_* : Hₙ₋₁(S(p^⊥); ℤ) ≅ Hₙ₋₁(Ω_p Sⁿ; ℤ)`. As `S(p^⊥)` is a sphere of dimension `n - 1`, this says
that `λ_*` sends the fundamental class of `S(p^⊥)` to a generator of `Hₙ₋₁(Ω_p Sⁿ; ℤ) ≅ ℤ`. -/
theorem isIso_singularHomologyFunctor_map_meridianLoopFixedReturn {m : ℕ}
    (hE : finrank ℝ E = m + 3)
    (u₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (meridianLoopFixedReturn p u₀))) := by
  let R := ModuleCat.of ℤ ℤ
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have hp0 : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hV : finrank ℝ (ℝ ∙ (p : E))ᗮ = m + 1 + 1 := by
    have : Fact (finrank ℝ E = m + 2 + 1) := ⟨hE⟩
    exact Submodule.finrank_orthogonal_span_singleton hp0
  -- A generalized loop `c` of `S(p^⊥)` that is a homeomorphism off the boundary of its cube.
  obtain ⟨c, hcs, hci⟩ := exists_genLoop_sphere hV u₀
  have hc : IsIso (GenLoop.hurewicz R c) := GenLoop.isIso_hurewicz_of_forall_ne R hcs hci
  -- Read through the meridian loops, `c` becomes a generalized loop `f` of `Ω_p Sⁿ` at
  -- `γ_{u₀} · γ_{u₀}⁻¹`. Transported to the constant loop, it has a generating Hurewicz class,
  -- since its shift to the sphere does.
  set f := GenLoop.map (meridianLoopFixedReturn p u₀) (meridianLoopFixedReturn_apply p u₀ u₀) c
  have hg := (HomotopyGroup.isIso_hurewicz_genLoopLoopHomeomorph_iff (n := m)
    (fun k hk ↦ subsingleton_homotopyGroup_sphere_of_lt (n := m + 2) hE (by simpa using hk) p)
    (GenLoop.transport (meridianContraction p u₀).symm f)).1
    (isIso_hurewicz_meridianCube p hE u₀ c hcs hci)
  -- Transport does not change Hurewicz classes, and the class of `f` is that of `c` read
  -- through the meridian loops.
  have hgf : GenLoop.hurewicz R (GenLoop.transport (meridianContraction p u₀).symm f) =
      GenLoop.hurewicz R f := by
    rw [← HomotopyGroup.hurewicz_mk, ← HomotopyGroup.hurewicz_mk, ← homotopyGroupTransport_mk]
    exact HomotopyGroup.hurewicz_homotopyGroupTransport R m _ _
  rw [hgf, GenLoop.hurewicz_map] at hg
  exact IsIso.of_isIso_comp_left (GenLoop.hurewicz R c) _

end TauCeti
