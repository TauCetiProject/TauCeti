/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Compression
public import TauCeti.Topology.Homotopy.SerreFibration.RelativeCube

/-!
# Connectivity of preimage pairs under a Serre fibration

Let `p : E → B` be a Serre fibration and `A ⊆ B`. The pair `(E, p⁻¹(A))` is at least as highly
connected as the pair `(B, A)`:

* if the relative homotopy set `π_{n+1}(B, A, p e)` is trivial, so is `π_{n+1}(E, p⁻¹(A), e)`
  (`TauCeti.TopCat.subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations`);
* if every point of `B` is joined by a path to a point of `A`, every point of `E` is joined by a
  path to a point of `p⁻¹(A)` (`TauCeti.TopCat.exists_joined_preimage_of_mem_serreFibrations`).

So a Serre fibration pulls `n`-connected pairs back to `n`-connected pairs. For the skeleta
`Xⁱ ⊆ Xⁱ⁺¹` of a CW complex this says that the pairs `(p⁻¹(Xⁱ⁺¹), p⁻¹(Xⁱ))` of the skeletal
filtration of a fibration over `X` are `i`-connected, which is what places the first page of its
spectral sequence in nonnegative fibre degrees.

## Main results

* `TauCeti.TopCat.subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations`:
  `π_{n+1}(E, p⁻¹(A), e)` is trivial when `π_{n+1}(B, A, p e)` is.
* `TauCeti.TopCat.exists_joined_preimage_of_mem_serreFibrations`: points of `E` are joined to
  `p⁻¹(A)` when points of `B` are joined to `A`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the proof of Theorem 4.41 (relative homotopy groups of a fibration and of its
  base).
-/

public section

universe u v

open CategoryTheory Set
open scoped unitInterval Topology.Homotopy

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- **A Serre fibration pulls back trivial relative homotopy sets.** If `p : E ⟶ B` is a Serre
fibration, `A ⊆ B` and `e ∈ p⁻¹(A)`, and the relative homotopy set `π_{n+1}(B, A, p e)` is
trivial, then so is `π_{n+1}(E, p⁻¹(A), e)`, where `n` is the cardinality of `N`. -/
theorem subsingleton_relHomotopyGroup_preimage_of_mem_serreFibrations (hp : serreFibrations p)
    {N : Type v} [Finite N] {A : Set B} (e : p ⁻¹' A)
    (h : Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset A, ⟨p e, e.2⟩⟩)) :
    Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset (p ⁻¹' A), e⟩) := by
  refine RelHomotopyGroup.subsingleton_iff.2 fun γ ↦ ?_
  -- The projection of `γ` is a relative cube of `(B, A, p e)`.
  let π : (⟨TopPair.ofSubset (p ⁻¹' A), e⟩ : BasedTopPair) ⟶ ⟨TopPair.ofSubset A, ⟨p e, e.2⟩⟩ :=
    ⟨TopPair.ofSubsetMap p fun _ h ↦ h, Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)⟩
  let q := RelGenLoop.map π γ
  have hq (z : I × (N → I)) : q.1 z = p (γ.1 z) :=
    (RelGenLoop.map_apply π γ z).trans (TopPair.ofSubsetMap_fst_apply _ _ _)
  obtain ⟨q', ⟨F⟩, hq'⟩ := RelHomotopyGroup.subsingleton_iff.1 h q
  -- Lift the compression `F` of `q`, read on the cube `I^(Option N)`, starting at `γ` and
  -- stationary on the boundary of the cube.
  let φ := piOptionEquivProdHomeomorph (fun _ : Option N ↦ I)
  let f : C(cylinderExtensionDomain (Cube.boundary (Option N)), E) :=
    γ.1.comp ((φ : C(Option N → I, I × (N → I))).comp
      (ContinuousMap.snd.comp ⟨Subtype.val, by fun_prop⟩))
  have hf₀ (x) : f x = γ.1 (φ x.1.2) := rfl
  let H : C(I × (Option N → I), B) :=
    ⟨fun x ↦ F (x.1, φ x.2), (map_continuous F).comp (by fun_prop)⟩
  have hf : ∀ x, p (f x) = H x := by
    rintro ⟨⟨s, y⟩, hx⟩
    obtain hx | hx := mem_cylinderExtensionDomain_iff.1 hx
    · obtain rfl : s = 0 := hx
      exact ((F.apply_zero (φ y)).trans (hq _)).symm
    · exact ((F.eq_fst s (piOptionEquivProdHomeomorph_mem_prodBoundary_iff.2 hx)).trans
        (hq _)).symm
  obtain ⟨G, hG, hGf⟩ := exists_lift_openBox_of_mem_serreFibrations hp (Option N) f H hf
  have hG' (x : I × (Option N → I)) : p (G x) = F (x.1, φ x.2) := congrFun hG x
  refine ⟨⟨fun z ↦ G (1, φ.symm z), (map_continuous G).comp (by fun_prop)⟩,
    ⟨{ toFun := fun x ↦ G (x.1, φ.symm x.2)
       continuous_toFun := (map_continuous G).comp (by fun_prop)
       map_zero_left := fun z ↦
         (hGf ⟨(0, φ.symm z), zero_mem_cylinderExtensionDomain _⟩).trans
           (by rw [hf₀, Homeomorph.apply_symm_apply])
       map_one_left := fun _ ↦ rfl
       prop' := fun s z hz ↦ by
         have hz' : φ.symm z ∈ Cube.boundary (Option N) := by
           rw [← piOptionEquivProdHomeomorph_mem_prodBoundary_iff]
           simpa [φ] using hz
         exact (hGf ⟨(s, φ.symm z), mem_cylinderExtensionDomain_of_mem hz'⟩).trans
           (by rw [hf₀, Homeomorph.apply_symm_apply]) }⟩, fun z ↦ ?_⟩
  -- The end of the lift lies over `A`.
  obtain ⟨a, ha⟩ := hq' z
  refine ⟨⟨G (1, φ.symm z), ?_⟩, rfl⟩
  have := hG' (1, φ.symm z)
  simp only [Homeomorph.apply_symm_apply, F.apply_one] at this
  rw [mem_preimage, this, ← ha]
  exact a.2

/-- **A Serre fibration pulls back path-connectedness to a subspace.** If `p : E ⟶ B` is a Serre
fibration and every point of `B` is joined by a path to a point of `A ⊆ B`, then every point of
`E` is joined by a path to a point of `p⁻¹(A)`. -/
theorem exists_joined_preimage_of_mem_serreFibrations (hp : serreFibrations p) {A : Set B}
    (h : ∀ b : B, ∃ a ∈ A, Joined b a) (x : E) : ∃ y ∈ p ⁻¹' A, Joined x y := by
  obtain ⟨a, ha, ⟨γ⟩⟩ := h (p x)
  obtain ⟨Γ, hΓ₀, hΓ⟩ := exists_path_lift_of_mem_serreFibrations hp γ
  refine ⟨Γ 1, ?_, ⟨⟨Γ, hΓ₀, rfl⟩⟩⟩
  have hΓ₁ := congrFun hΓ 1
  rw [Function.comp_apply] at hΓ₁
  rw [mem_preimage, hΓ₁, γ.target]
  exact ha

end TopCat

end TauCeti
