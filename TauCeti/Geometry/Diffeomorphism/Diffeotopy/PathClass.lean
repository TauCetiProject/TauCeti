/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Group
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homotopy

/-!
# Path classes of diffeotopies through a subgroup

Let `S` be a subgroup of the group of self-diffeomorphisms of a manifold `M`, for instance the
symplectomorphisms of a symplectic form, and consider the diffeotopies `φ_t` all of whose time
slices lie in `S` (`TauCeti.Diffeotopy.sliceSubgroup S`). Two such diffeotopies `φ_t` and `ψ_t` are
**homotopic through `S`** (`TauCeti.Diffeotopy.HomotopicWith S`) when they are joined by a homotopy
fixing both time ends (`TauCeti.Diffeotopy.Homotopic`) all of whose intermediate maps lie in `S`:
a smooth map `G : (M × [0, 1]) × [0, 1] → M` with a smooth inverse in the space variable, joining
the motion `(x, t) ↦ φ_t x` at `s = 0` to that of `ψ_t` at `s = 1`, with `G ((x, 0), s) = x` and
`G ((x, 1), s) = φ₁ x`, and such that every map `x ↦ G ((x, t), s)` is an element of `S`. For the
symplectomorphism group these are the homotopies of symplectic isotopies through symplectic
isotopies.

Homotopy through `S` is an equivalence relation on the diffeotopies through `S`
(`TauCeti.Diffeotopy.HomotopicWith.refl`, `TauCeti.Diffeotopy.HomotopicWith.symm`,
`TauCeti.Diffeotopy.HomotopicWith.trans`), compatible with the pointwise product
`(φ ψ)_t = φ_t ∘ ψ_t` (`TauCeti.Diffeotopy.HomotopicWith.mul_congr`). So it is a congruence on the
group `sliceSubgroup S` (`TauCeti.Diffeotopy.homotopicWithCon`), and its quotient is the group of
**path classes through `S`** (`TauCeti.Diffeotopy.PathClass S`): the paths from the identity in
`S`, modulo homotopy in `S` fixing both ends, with the pointwise product. Homotopic diffeotopies end
at the same diffeomorphism, so the final diffeomorphism descends to a homomorphism
(`TauCeti.Diffeotopy.PathClass.final`), whose image is the group of final diffeomorphisms of
diffeotopies through `S` (`TauCeti.Diffeotopy.PathClass.range_final`) and whose kernel consists of
the classes of loops.

The diffeotopies are those of `TauCeti.Diffeotopy`; they are not required to be constant near the
ends of the time interval.

## Main definitions

* `TauCeti.Diffeotopy.HomotopicWith S`: homotopy of diffeotopies fixing both time ends through
  maps in `S`.
* `TauCeti.Diffeotopy.homotopicWithCon S`: homotopy through `S` as a congruence on the group of
  diffeotopies through `S`.
* `TauCeti.Diffeotopy.PathClass S`: the group of path classes through `S`.
* `TauCeti.Diffeotopy.PathClass.mk`, `TauCeti.Diffeotopy.PathClass.final`: the class of a
  diffeotopy, and the final diffeomorphism of a class.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (homotopy classes of symplectic isotopies with fixed end
  points, and the universal cover of the identity component of the symplectomorphism group).
-/

public section

noncomputable section

namespace TauCeti

namespace Diffeotopy

open unitInterval
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {S : Subgroup (M ≃ₘ^n⟮J, J⟯ M)} {Φ Φ' Ψ Ψ' Θ : Diffeotopy J n M}

variable (S) in
/-- Two diffeotopies are **homotopic through** a subgroup `S` of self-diffeomorphisms when they
are joined by a homotopy fixing both time ends all of whose intermediate maps lie in `S`. That is,
a `C^n` map `G : (M × [0, 1]) × [0, 1] → M` joins the motion `(x, t) ↦ φ_t x` of `Φ` at `s = 0` to
the motion of `Ψ` at `s = 1`, fixes both time ends, `G ((x, 0), s) = x` and `G ((x, 1), s) = φ₁ x`,
has a `C^n` inverse `G'` in the space variable (`TauCeti.Diffeotopy.IsHomotopy`), and every map
`x ↦ G ((x, t), s)` is an element of `S`. Forgetting the last condition gives
`TauCeti.Diffeotopy.Homotopic`. -/
def HomotopicWith (Φ Ψ : Diffeotopy J n M) : Prop :=
  ∃ G G' : (M × I) × I → M, IsHomotopy Φ Ψ G G' ∧ ∀ t s, ∃ f ∈ S, ⇑f = fun x ↦ G ((x, t), s)

/-- Unfold homotopy through `S`: a homotopy of diffeotopies fixing both time ends, with a `C^n`
inverse in the space variable, all of whose intermediate maps lie in `S`. -/
theorem homotopicWith_iff : HomotopicWith S Φ Ψ ↔
    ∃ G G' : (M × I) × I → M, IsHomotopy Φ Ψ G G' ∧ ∀ t s, ∃ f ∈ S, ⇑f = fun x ↦ G ((x, t), s) :=
  Iff.rfl

/-- Diffeotopies homotopic through `S` are homotopic. -/
theorem HomotopicWith.homotopic (h : HomotopicWith S Φ Ψ) : Φ.Homotopic Ψ := by
  obtain ⟨G, G', h, -⟩ := h
  exact h.homotopic

/-- Diffeotopies homotopic through `S` have the same final diffeomorphism. -/
theorem HomotopicWith.final_eq (h : HomotopicWith S Φ Ψ) : Φ.final = Ψ.final :=
  h.homotopic.final_eq

/-- A homotopy through a smaller subgroup is a homotopy through a larger one. -/
theorem HomotopicWith.mono {S' : Subgroup (M ≃ₘ^n⟮J, J⟯ M)} (hS : S ≤ S')
    (h : HomotopicWith S Φ Ψ) : HomotopicWith S' Φ Ψ := by
  obtain ⟨G, G', h, hS'⟩ := h
  refine ⟨G, G', h, fun t s ↦ ?_⟩
  obtain ⟨f, hf, hfG⟩ := hS' t s
  exact ⟨f, hS hf, hfG⟩

/-- A diffeotopy through `S` is homotopic through `S` to itself, through the constant
homotopy. -/
theorem HomotopicWith.refl (hΦ : Φ ∈ sliceSubgroup S) : HomotopicWith S Φ Φ :=
  ⟨_, _, IsHomotopy.refl Φ, fun t _ ↦ ⟨Φ.timeSlice t, mem_sliceSubgroup.1 hΦ t, funext fun x ↦ by
    dsimp only
    rw [cylinderMap_apply, timeSlice_apply]⟩⟩

/-- Homotopy through `S` is symmetric: run the homotopy backwards. -/
theorem HomotopicWith.symm (h : HomotopicWith S Φ Ψ) : HomotopicWith S Ψ Φ := by
  obtain ⟨G, K, h, hS⟩ := h
  exact ⟨_, _, h.symm, fun t s ↦ hS t (σ s)⟩

/-- **Homotopy through `S` is transitive**, at finite regularity and at `C^∞`: glue the two
homotopies, each reparametrized to be stationary near the joining time. -/
theorem HomotopicWith.trans (h : HomotopicWith S Φ Ψ) (h' : HomotopicWith S Ψ Θ) (hn : n ≤ ∞) :
    HomotopicWith S Φ Θ := by
  obtain ⟨G, K, h, hS⟩ := h
  obtain ⟨G', K', h', hS'⟩ := h'
  refine ⟨_, _, h.trans h' hn, fun t s ↦ ?_⟩
  -- At a fixed homotopy time the glued map is a slice of one of the two homotopies.
  dsimp only
  split_ifs
  exacts [hS t _, hS' t _]

/-- **Homotopy through `S` is compatible with the pointwise product.** If `Φ` is homotopic through
`S` to `Φ'` and `Ψ` to `Ψ'`, then `φ_t ∘ ψ_t` is homotopic through `S` to `φ'_t ∘ ψ'_t`. -/
theorem HomotopicWith.mul_congr (h : HomotopicWith S Φ Φ') (h' : HomotopicWith S Ψ Ψ') :
    HomotopicWith S (Φ * Ψ) (Φ' * Ψ') := by
  obtain ⟨G, K, h', hS⟩ := h'
  obtain ⟨G', K', h, hS'⟩ := h
  refine ⟨_, _, mul_def Φ Ψ ▸ mul_def Φ' Ψ' ▸ h'.trans_congr h, fun t s ↦ ?_⟩
  -- The intermediate maps are the composites of those of the two homotopies.
  obtain ⟨f, hf, hfG⟩ := hS t s
  obtain ⟨f', hf', hf'G⟩ := hS' t s
  refine ⟨f' * f, S.mul_mem hf' hf, ?_⟩
  rw [Diffeomorph.coe_mul, hfG, hf'G]
  rfl

variable (S) in
/-- **Homotopy through `S` as a congruence** on the group of diffeotopies through `S`, for
`n ≤ ∞`. -/
def homotopicWithCon (hn : n ≤ ∞) : Con (sliceSubgroup S) where
  r Φ Ψ := HomotopicWith S Φ Ψ
  iseqv := ⟨fun Φ ↦ HomotopicWith.refl Φ.property, HomotopicWith.symm,
    fun h h' ↦ h.trans h' hn⟩
  mul' h h' := HomotopicWith.mul_congr h h'

/-- Two diffeotopies through `S` are related by the congruence exactly when they are homotopic
through `S`. -/
@[simp]
theorem homotopicWithCon_apply (hn : n ≤ ∞) (Φ Ψ : sliceSubgroup S) :
    homotopicWithCon S hn Φ Ψ ↔ HomotopicWith S Φ Ψ :=
  Iff.rfl

variable (S) in
/-- The **group of path classes through `S`**: the diffeotopies all of whose time slices lie in
`S`, modulo homotopy through `S` fixing both time ends, with the pointwise product
`(φ ψ)_t = φ_t ∘ ψ_t`. For the stabilizer of a symplectic form these are the classes of
symplectic isotopies starting at the identity. -/
abbrev PathClass (hn : n ≤ ∞) : Type _ :=
  (homotopicWithCon S hn).Quotient

namespace PathClass

variable (hn : n ≤ ∞)

variable (S) in
/-- The path class of a diffeotopy through `S`, as a group homomorphism. -/
def mk : sliceSubgroup S →* PathClass S hn :=
  (homotopicWithCon S hn).mk'

variable {hn}

/-- The path class of a diffeotopy is its class for the congruence `homotopicWithCon S hn`. -/
theorem mk_def (Φ : sliceSubgroup S) : mk S hn Φ = (homotopicWithCon S hn).mk' Φ :=
  (rfl)

/-- Every path class is the class of a diffeotopy through `S`. -/
theorem mk_surjective : Function.Surjective (mk S hn) :=
  (homotopicWithCon S hn).mk'_surjective

/-- Two diffeotopies through `S` have the same path class exactly when they are homotopic through
`S`. -/
@[simp]
theorem mk_eq_mk_iff {Φ Ψ : sliceSubgroup S} : mk S hn Φ = mk S hn Ψ ↔ HomotopicWith S Φ Ψ :=
  (homotopicWithCon S hn).eq

variable (S hn) in
/-- The **final diffeomorphism of a path class**: homotopic diffeotopies have the same final
diffeomorphism. -/
def final : PathClass S hn →* M ≃ₘ^n⟮J, J⟯ M :=
  (homotopicWithCon S hn).lift ((finalHom J n M).comp (sliceSubgroup S).subtype)
    fun _ _ h ↦ (Con.ker_rel _).2 (by
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, finalHom_apply]
      exact HomotopicWith.final_eq h)

/-- The final diffeomorphism of the class of a diffeotopy is its final diffeomorphism. -/
@[simp]
theorem final_mk (Φ : sliceSubgroup S) : final S hn (mk S hn Φ) = (Φ : Diffeotopy J n M).final := by
  rw [mk_def, final, Con.lift_mk']
  exact finalHom_apply _

/-- The final diffeomorphism of a path class lies in `S`. -/
theorem final_mem (γ : PathClass S hn) : final S hn γ ∈ S := by
  obtain ⟨Φ, rfl⟩ := mk_surjective γ
  rw [final_mk]
  exact final_mem_of_mem_sliceSubgroup Φ.property

/-- **The image of the final diffeomorphism** consists of the final diffeomorphisms of the
diffeotopies through `S`. -/
theorem range_final :
    (final S hn).range = (sliceSubgroup S).map (finalHom J n M) := by
  ext φ
  simp only [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨Φ, rfl⟩ := mk_surjective γ
    exact ⟨Φ, Φ.property, by rw [final_mk, finalHom_apply]⟩
  · rintro ⟨Φ, hΦ, rfl⟩
    exact ⟨mk S hn ⟨Φ, hΦ⟩, by rw [final_mk, finalHom_apply]⟩

end PathClass

end Diffeotopy

end TauCeti
