/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit

/-!
# Cohomological units for `A∞` algebras

A cohomological unit is a degree-zero cycle whose left and right binary products act as the
identity modulo boundaries.  Unlike a strict unit, its unit equations therefore hold only after
passing to the cohomology of the unary operation, and it places no restriction on higher
operations containing its chosen representative.

The characteristic API for a cohomological unit is stated both in terms of explicit boundaries and
as the two unit laws for the product `AInfinityAlgebra.cohomologyMul` on the total cohomology
module.  In particular, any two representatives of a cohomological unit determine the same class,
every strict unit supplies a cohomological one, cohomological unitality is invariant under `A∞`
quasi-isomorphism, and on a minimal `A∞` algebra a cohomological unit is already a strict
two-sided unit for `m₂`.

## Main definitions

* `TauCeti.AInfinityAlgebra.CohomologicalUnit`: a representative of a two-sided unit in
  cohomology.
* `TauCeti.AInfinityAlgebra.CohomologicallyUnital`: existence of such a representative.

## Main results

* `TauCeti.AInfinityHom.IsQuasiIso.cohomologicalUnit` and
  `TauCeti.AInfinityHom.IsQuasiIso.cohomologicallyUnital_iff`: invariance of cohomological units
  and cohomological unitality along `A∞` quasi-isomorphisms.
* `TauCeti.AInfinityAlgebra.IsMinimal.cohomologicalUnit_iff` and
  `TauCeti.AInfinityAlgebra.IsMinimal.cohomologicalUnit_of_m_two_eq`: on a minimal `A∞` algebra,
  cohomological units are degree-zero two-sided units for `m₂` and depend only on the grading and
  `m₂`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.3, and 3.6.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Cohomological units -/

/-- A chain representative of a unit on the cohomology of an `A∞` algebra.

The representative is a degree-zero cycle.  Its binary products with every cycle differ from that
cycle by an explicit unary boundary, on both the left and the right.  These equations neither
select a strict chain-level unit nor constrain higher operations on tuples containing `e`. -/
structure CohomologicalUnit (𝒜 : AInfinityAlgebra R A) (e : A) : Prop where
  /-- The representative has cohomological degree zero. -/
  degree_zero : e ∈ 𝒜.grading.piece 0
  /-- The representative is a unary cycle. -/
  cycle : e ∈ 𝒜.cycles
  /-- Left multiplication by the representative is the identity modulo boundaries. -/
  left_unit : ∀ x : A, x ∈ 𝒜.cycles → 𝒜.m 2 ![e, x] - x ∈ 𝒜.boundaries
  /-- Right multiplication by the representative is the identity modulo boundaries. -/
  right_unit : ∀ x : A, x ∈ 𝒜.cycles → 𝒜.m 2 ![x, e] - x ∈ 𝒜.boundaries

/-- An `A∞` algebra is cohomologically unital when it admits a cohomological-unit
representative. -/
def CohomologicallyUnital (𝒜 : AInfinityAlgebra R A) : Prop :=
  ∃ e : A, 𝒜.CohomologicalUnit e

/-- Unfolding `CohomologicallyUnital`: existence of a cohomological-unit representative. -/
theorem cohomologicallyUnital_def (𝒜 : AInfinityAlgebra R A) :
    𝒜.CohomologicallyUnital ↔ ∃ e : A, 𝒜.CohomologicalUnit e :=
  Iff.rfl

namespace CohomologicalUnit

variable {𝒜 : AInfinityAlgebra R A} {e e' : A}

/-- Any cohomological-unit representative witnesses that the algebra is cohomologically unital. -/
theorem cohomologicallyUnital (h : 𝒜.CohomologicalUnit e) : 𝒜.CohomologicallyUnital :=
  ⟨e, h⟩

/-- A cohomological-unit representative has degree `-1` in the suspended grading. -/
theorem mem_shift_one_piece (h : 𝒜.CohomologicalUnit e) : e ∈ (𝒜.grading.shift 1).piece (-1) :=
  𝒜.grading.mem_shift_piece_neg_of_mem_zero 1 h.degree_zero

/-- The explicit-boundary form of the left unit equation. -/
theorem exists_differential_eq_left_sub (h : 𝒜.CohomologicalUnit e) {x : A}
    (hx : x ∈ 𝒜.cycles) : ∃ y : A, 𝒜.m 1 ![y] = 𝒜.m 2 ![e, x] - x :=
  (𝒜.mem_boundaries).mp (h.left_unit x hx)

/-- The explicit-boundary form of the right unit equation. -/
theorem exists_differential_eq_right_sub (h : 𝒜.CohomologicalUnit e) {x : A}
    (hx : x ∈ 𝒜.cycles) : ∃ y : A, 𝒜.m 1 ![y] = 𝒜.m 2 ![x, e] - x :=
  (𝒜.mem_boundaries).mp (h.right_unit x hx)

/-- The class of a cohomological unit is a left unit for the product on cohomology. -/
@[simp]
theorem cohomologyMul_cohomologyClass_left (h : 𝒜.CohomologicalUnit e) (c : 𝒜.Cohomology) :
    𝒜.cohomologyMul (𝒜.cohomologyClass h.cycle) c = c := by
  obtain ⟨x, hx, rfl⟩ := 𝒜.exists_cohomologyClass_eq c
  simpa using h.left_unit x hx

/-- The class of a cohomological unit is a right unit for the product on cohomology. -/
@[simp]
theorem cohomologyMul_cohomologyClass_right (h : 𝒜.CohomologicalUnit e) (c : 𝒜.Cohomology) :
    𝒜.cohomologyMul c (𝒜.cohomologyClass h.cycle) = c := by
  obtain ⟨x, hx, rfl⟩ := 𝒜.exists_cohomologyClass_eq c
  simpa using h.right_unit x hx

/-- Any two cohomological-unit representatives differ by a boundary. -/
theorem sub_mem_boundaries (h : 𝒜.CohomologicalUnit e) (h' : 𝒜.CohomologicalUnit e') :
    e - e' ∈ 𝒜.boundaries := by
  have hleft := h.left_unit e' h'.cycle
  have hright := h'.right_unit e h.cycle
  simpa only [sub_sub_sub_cancel_left] using 𝒜.boundaries.sub_mem hleft hright

/-- Any two cohomological-unit representatives determine the same cohomology class. -/
theorem cohomologyClass_eq (h : 𝒜.CohomologicalUnit e) (h' : 𝒜.CohomologicalUnit e') :
    𝒜.cohomologyClass h.cycle = 𝒜.cohomologyClass h'.cycle :=
  (𝒜.cohomologyClass_eq_iff _ _).mpr (h.sub_mem_boundaries h')

/-- A degree-zero cycle whose cohomology class is a two-sided unit for `cohomologyMul` is a
cohomological unit. -/
theorem of_cohomologyMul (hdeg : e ∈ 𝒜.grading.piece 0) (hcyc : e ∈ 𝒜.cycles)
    (hl : ∀ c : 𝒜.Cohomology, 𝒜.cohomologyMul (𝒜.cohomologyClass hcyc) c = c)
    (hr : ∀ c : 𝒜.Cohomology, 𝒜.cohomologyMul c (𝒜.cohomologyClass hcyc) = c) :
    𝒜.CohomologicalUnit e where
  degree_zero := hdeg
  cycle := hcyc
  left_unit x hx := (𝒜.cohomologyClass_eq_iff (𝒜.m_two_mem_cycles hcyc hx) hx).mp <| by
    rw [← 𝒜.cohomologyMul_cohomologyClass hcyc hx, hl]
  right_unit x hx := (𝒜.cohomologyClass_eq_iff (𝒜.m_two_mem_cycles hx hcyc) hx).mp <| by
    rw [← 𝒜.cohomologyMul_cohomologyClass hx hcyc, hr]

/-- A degree-zero cycle with the same cohomology class as a cohomological unit is itself a
cohomological unit. -/
theorem of_cohomologyClass_eq (h : 𝒜.CohomologicalUnit e)
    (hdeg : e' ∈ 𝒜.grading.piece 0) (hcyc : e' ∈ 𝒜.cycles)
    (heq : 𝒜.cohomologyClass hcyc = 𝒜.cohomologyClass h.cycle) :
    𝒜.CohomologicalUnit e' :=
  of_cohomologyMul hdeg hcyc
    (fun c ↦ by rw [heq, h.cohomologyMul_cohomologyClass_left])
    (fun c ↦ by rw [heq, h.cohomologyMul_cohomologyClass_right])

end CohomologicalUnit

namespace StrictUnit

variable {𝒜 : AInfinityAlgebra R A} {e : A}

/-- A strict unit is a cohomological unit, represented by the same element. -/
theorem cohomologicalUnit (h : 𝒜.StrictUnit e) : 𝒜.CohomologicalUnit e where
  degree_zero := h.degree_zero
  cycle := 𝒜.mem_cycles.mpr h.unary_eq_zero
  left_unit x _ := by simp only [h.binary_left, sub_self, Submodule.zero_mem]
  right_unit x _ := by simp only [h.binary_right, sub_self, Submodule.zero_mem]

/-- An `A∞` algebra with a strict unit is cohomologically unital. -/
theorem cohomologicallyUnital (h : 𝒜.StrictUnit e) : 𝒜.CohomologicallyUnital :=
  ⟨e, h.cohomologicalUnit⟩

end StrictUnit

/-! ### Cohomological units on minimal `A∞` algebras -/

section Minimal

variable {𝒜 : AInfinityAlgebra R A} {e : A}

/-- On a minimal `A∞` algebra, a cohomological unit is a strict left unit for `m₂`. -/
theorem IsMinimal.cohomologicalUnit_binary_left (h𝒜 : 𝒜.IsMinimal) (he : 𝒜.CohomologicalUnit e)
    (x : A) : 𝒜.m 2 ![e, x] = x := by
  have h := he.left_unit x (h𝒜.mem_cycles x)
  rwa [(isMinimal_iff_boundaries_eq_bot 𝒜).mp h𝒜, Submodule.mem_bot, sub_eq_zero] at h

/-- On a minimal `A∞` algebra, a cohomological unit is a strict right unit for `m₂`. -/
theorem IsMinimal.cohomologicalUnit_binary_right (h𝒜 : 𝒜.IsMinimal) (he : 𝒜.CohomologicalUnit e)
    (x : A) : 𝒜.m 2 ![x, e] = x := by
  have h := he.right_unit x (h𝒜.mem_cycles x)
  rwa [(isMinimal_iff_boundaries_eq_bot 𝒜).mp h𝒜, Submodule.mem_bot, sub_eq_zero] at h

/-- On a minimal `A∞` algebra, `e` is a cohomological unit iff it has degree zero and is a
two-sided unit for `m₂`. -/
theorem IsMinimal.cohomologicalUnit_iff (h𝒜 : 𝒜.IsMinimal) :
    𝒜.CohomologicalUnit e ↔
      e ∈ 𝒜.grading.piece 0 ∧ (∀ x, 𝒜.m 2 ![e, x] = x) ∧ (∀ x, 𝒜.m 2 ![x, e] = x) :=
  ⟨fun he ↦ ⟨he.degree_zero, h𝒜.cohomologicalUnit_binary_left he,
    h𝒜.cohomologicalUnit_binary_right he⟩,
   fun ⟨hdeg, hl, hr⟩ ↦ ⟨hdeg, h𝒜.mem_cycles e,
    fun x _ ↦ by rw [hl, sub_self]; exact Submodule.zero_mem _,
    fun x _ ↦ by rw [hr, sub_self]; exact Submodule.zero_mem _⟩⟩

/-- On a minimal `A∞` algebra with cohomological unit `e`, `𝒜.taylor` sends `[e, y]` to `y`. -/
theorem IsMinimal.taylor_of_two_cohomologicalUnit_left (h𝒜 : 𝒜.IsMinimal)
    (he : 𝒜.CohomologicalUnit e) (y : A) :
    𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![e, y])) = y := by
  rw [taylor_of_two, 𝒜.grading.koszulTwist_apply_of_mem_zero he.degree_zero,
    h𝒜.cohomologicalUnit_binary_left he]

/-- On a minimal `A∞` algebra with cohomological unit `e`, `𝒜.taylor` sends `[y, e]` to
`𝒜.grading.koszulTwist 1 y`. -/
theorem IsMinimal.taylor_of_two_cohomologicalUnit_right (h𝒜 : 𝒜.IsMinimal)
    (he : 𝒜.CohomologicalUnit e) (y : A) :
    𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![y, e])) =
      𝒜.grading.koszulTwist 1 y := by
  rw [taylor_of_two, h𝒜.cohomologicalUnit_binary_right he]

/-- If `0` is a cohomological unit of a minimal `A∞` algebra, then `0` is already a strict unit. -/
theorem IsMinimal.strictUnit_zero_of_cohomologicalUnit_zero (h𝒜 : 𝒜.IsMinimal)
    (he : 𝒜.CohomologicalUnit 0) : 𝒜.StrictUnit 0 := by
  have hall : ∀ x : A, x = 0 := fun x ↦ by
    rw [← h𝒜.cohomologicalUnit_binary_left he x]; exact (𝒜.m 2).map_coord_zero 0 rfl
  exact ⟨Submodule.zero_mem _, fun x ↦ by rw [hall x, hall (𝒜.m 2 _)],
    fun x ↦ by rw [hall x, hall (𝒜.m 2 _)], fun _ _ _ _ ↦ hall _⟩

/-- Minimal `A∞` structures with the same grading and `m 2` have the same cohomological units. -/
theorem IsMinimal.cohomologicalUnit_of_m_two_eq {𝒜' : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    (h𝒜' : 𝒜'.IsMinimal) (hG : 𝒜'.grading = 𝒜.grading) (hm2 : 𝒜'.m 2 = 𝒜.m 2)
    (he : 𝒜.CohomologicalUnit e) : 𝒜'.CohomologicalUnit e :=
  h𝒜'.cohomologicalUnit_iff.2 ⟨hG ▸ he.degree_zero,
    fun x ↦ by rw [hm2, h𝒜.cohomologicalUnit_binary_left he],
    fun x ↦ by rw [hm2, h𝒜.cohomologicalUnit_binary_right he]⟩

/-- Minimal `A∞` structures with the same grading whose Taylor maps agree on `filtration R A n`
for some `2 ≤ n` have the same cohomological units. -/
theorem IsMinimal.cohomologicalUnit_of_taylor_eq {𝒜' : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    (h𝒜' : 𝒜'.IsMinimal) (hG : 𝒜'.grading = 𝒜.grading) {n : ℕ} (hn : 2 ≤ n)
    (htay : ∀ z ∈ ReducedTensorWords.filtration R A n, 𝒜'.taylor z = 𝒜.taylor z)
    (he : 𝒜.CohomologicalUnit e) : 𝒜'.CohomologicalUnit e :=
  h𝒜.cohomologicalUnit_of_m_two_eq h𝒜' hG (m_eq_of_taylor_eq_on_filtration hG hn htay) he

end Minimal

end AInfinityAlgebra

/-! ### Invariance under `A∞` quasi-isomorphism -/

namespace AInfinityHom

universe uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

private theorem cohomologyMap_cohomologyMul (f : AInfinityHom 𝒜 ℬ) (a b : 𝒜.Cohomology) :
    f.cohomologyMap (𝒜.cohomologyMul a b) =
      ℬ.cohomologyMul (f.cohomologyMap a) (f.cohomologyMap b) := by
  rw [← AInfinityAlgebra.cohomology_mul_eq_cohomologyMul, map_mul,
    AInfinityAlgebra.cohomology_mul_eq_cohomologyMul]

/-- The linear part of an `A∞` quasi-isomorphism preserves cohomological-unit representatives. -/
theorem IsQuasiIso.cohomologicalUnit {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) {e : A}
    (he : 𝒜.CohomologicalUnit e) : ℬ.CohomologicalUnit (f.linearPart e) :=
  AInfinityAlgebra.CohomologicalUnit.of_cohomologyMul (f.linearPart_mem he.degree_zero)
    (f.linearPart_mem_cycles he.cycle)
    (fun c ↦ by
      obtain ⟨c', rfl⟩ := ((isQuasiIso_def f).mp hf).2 c
      rw [← f.cohomologyMap_cohomologyClass he.cycle, ← cohomologyMap_cohomologyMul,
        he.cohomologyMul_cohomologyClass_left])
    (fun c ↦ by
      obtain ⟨c', rfl⟩ := ((isQuasiIso_def f).mp hf).2 c
      rw [← f.cohomologyMap_cohomologyClass he.cycle, ← cohomologyMap_cohomologyMul,
        he.cohomologyMul_cohomologyClass_right])

/-- Along an `A∞` quasi-isomorphism, a degree-zero cycle `e` is a cohomological unit iff
`f.linearPart e` is a cohomological unit. -/
theorem IsQuasiIso.cohomologicalUnit_iff {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) {e : A}
    (hdeg : e ∈ 𝒜.grading.piece 0) (hcyc : e ∈ 𝒜.cycles) :
    ℬ.CohomologicalUnit (f.linearPart e) ↔ 𝒜.CohomologicalUnit e := by
  have hinj := ((isQuasiIso_def f).mp hf).1
  refine ⟨fun he' ↦ AInfinityAlgebra.CohomologicalUnit.of_cohomologyMul hdeg hcyc
    (fun c ↦ hinj ?_) (fun c ↦ hinj ?_), hf.cohomologicalUnit⟩
  · rw [cohomologyMap_cohomologyMul, f.cohomologyMap_cohomologyClass hcyc,
      he'.cohomologyMul_cohomologyClass_left]
  · rw [cohomologyMap_cohomologyMul, f.cohomologyMap_cohomologyClass hcyc,
      he'.cohomologyMul_cohomologyClass_right]

/-- Cohomological unitality is invariant under `A∞` quasi-isomorphism over any commutative ring. -/
theorem IsQuasiIso.cohomologicallyUnital_iff {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    𝒜.CohomologicallyUnital ↔ ℬ.CohomologicallyUnital := by
  rw [𝒜.cohomologicallyUnital_def, ℬ.cohomologicallyUnital_def]
  refine ⟨fun ⟨e, he⟩ ↦ ⟨f.linearPart e, hf.cohomologicalUnit he⟩, fun ⟨e', he'⟩ ↦ ?_⟩
  obtain ⟨e, hecyc, hedeg, heq⟩ := 𝒜.mem_cohomologyGrading_piece_iff.mp
    (hf.cohomologyMapInv_mem_cohomologyGrading_piece
      (ℬ.cohomologyClass_mem_cohomologyGrading_piece he'.cycle he'.degree_zero))
  have hfcyc := f.linearPart_mem_cycles hecyc
  have hclass : ℬ.cohomologyClass hfcyc = ℬ.cohomologyClass he'.cycle := by
    rw [← f.cohomologyMap_cohomologyClass hecyc, heq]
    exact NonUnitalAlgHom.congr_fun hf.cohomologyMap_comp_cohomologyMapInv _
  exact ⟨e, (hf.cohomologicalUnit_iff hedeg hecyc).mp
    (he'.of_cohomologyClass_eq (f.linearPart_mem hedeg) hfcyc hclass)⟩

end AInfinityHom

end TauCeti
