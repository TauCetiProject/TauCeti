/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Continuation

/-!
# Attaching free generators to a row-finite twisted module along cycles

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)`, with free
differential graded left module `K_m = P →₀ A` (`TauCeti.RowFiniteTwistingCocycle`). Given a
further graded set `(Q, indQ)` and, for each `q : Q`, a cycle `a q` of `K_m` of total degree
`1 - indQ q`, one obtains a new free module on `P ⊕ Q` by **attaching a free generator `e_q` with
differential `a q`**. Its rows are those of `m` on `P` and `a q` on `e_q`
(`TauCeti.RowFiniteTwistingCocycle.attach`); the Maurer–Cartan equation for the new rows is
exactly the cycle condition `D (a q) = 0`
(`TauCeti.mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero`). This is the algebraic
cell attachment by which semi-free modules are built: a CW complex is built by attaching cells
along their boundary spheres, and Brown's twisted tensor product, the semi-free resolution of the
ground ring over the chains on a loop space, is built by attaching one free generator per cell
along a cycle representing its attaching map. The finite coefficients of `a q` are the row of the
new generator in the resulting twisting cocycle.

Writing a vector of the new module as `sumElim f g`, with `f : P →₀ A` on the old generators and
`g : Q →₀ A` on the new ones, the new differential is upper triangular
(`TauCeti.RowFiniteTwistingCocycle.attach_differential_sumElim`):

`D (sumElim f g) = sumElim (D_m f + a(g)) (d g)`,

where `a(g)` is the signed substitution `TauCeti.rowFiniteSignedMap` of the rows `a` and `d g` is
the coefficient differential. So `K_m` is a differential submodule, through relabelling along
`Sum.inl` (`TauCeti.RowFiniteTwistingCocycle.attach_differential_mapDomain_inl`), and the
differential induced on the coefficients of the new generators is the coefficient differential
alone, that of the free module on `Q` with zero rows. Relabelling along any map compatible
with the rows commutes with the twisted differentials
(`TauCeti.rowFiniteTwistedDifferential_mapDomain`).

Maps out of the attached module are built one cell at a time
(`TauCeti.RowFiniteTwistingCocycle.forall_linearCombination_attach_differential_iff`): given a map
`g` out of `K_m` to a differential graded left module commuting with the differentials, it
extends by sending `e_q` to `c q` exactly when `d (c q) = g (a q)`, that is, when `c q` bounds
the image of the attaching cycle. Attaching along rows that only involve generators of strictly
smaller index preserves one-sidedness
(`TauCeti.RowFiniteTwistingCocycle.attach_m_eq_zero_of_le`), which is what makes the index
filtration of an iterated attachment a filtration by subcomplexes.

The attached module sits in a sequence

`0 → K_m → K_{attach} → K_0(Q) → 0`

of differential graded left modules, where `K_0(Q)` is the free module on the new generators with
the zero cocycle, carrying the coefficient differential alone. The inclusion
(`TauCeti.RowFiniteTwistingCocycle.attachInclusion`) and the projection onto the new coordinates
(`TauCeti.RowFiniteTwistingCocycle.attachProjection`) are continuation cocycles, hence chain maps;
the inclusion is injective, its image is the kernel of the projection
(`TauCeti.RowFiniteTwistingCocycle.exact_linearCombination_attachInclusion_attachProjection`), and
the projection is onto. So the quotient by the old generators is a direct sum of shifted copies of
the algebra, one for each new generator, as for the relative chains of a CW pair.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6 (semifree modules).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uM uP uQ

variable {R : Type uR} {A : Type uA} {P : Type uP} {Q : Type uQ}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ} {indQ : Q → ℤ}

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 d P ind) (a : Q → P →₀ A)

omit [GradedAlgebra 𝒜] in
/-- The attached rows have the degrees required of a twisting cocycle. -/
private theorem attachRows_mem_graded (ha : ∀ q y, a q y ∈ 𝒜 (ind y - indQ q + 1)) (z w : P ⊕ Q) :
    mapDomain Sum.inl (Sum.elim m.m a z) w ∈ 𝒜 (Sum.elim ind indQ w - Sum.elim ind indQ z + 1) := by
  rcases w with y | q
  · rw [mapDomain_apply_of_injective Sum.inl_injective]
    rcases z with x | q
    · exact m.mem_graded x y
    · exact ha q y
  · rw [mapDomain_of_notMem_range _ _ (by simp)]
    exact zero_mem _

/-- **Attaching free generators along cycles.** The generators `Q` are attached to the free
module of `m`, the generator `q` of index `indQ q` with differential the cycle `a q` of total
degree `1 - indQ q`. The rows of the old generators are unchanged, and those of the new
generators are the attaching cycles, both relabelled along `Sum.inl`. -/
noncomputable def attach (ha : ∀ q y, a q y ∈ 𝒜 (ind y - indQ q + 1))
    (hca : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (a q) = 0) :
    RowFiniteTwistingCocycle 𝒜 d (P ⊕ Q) (Sum.elim ind indQ) where
  m z := mapDomain Sum.inl (Sum.elim m.m a z)
  mem_graded := attachRows_mem_graded m a ha
  twisting z := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
      (attachRows_mem_graded m a ha z)).mpr ?_
    rw [rowFiniteTwistedDifferential_mapDomain Sum.inl m.m (fun _ ↦ rfl)]
    rcases z with x | q
    · simp [m.differential_row x]
    · simp [hca q]

variable {a} (ha : ∀ q y, a q y ∈ 𝒜 (ind y - indQ q + 1))
  (hca : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (a q) = 0)

/-- The row of an old generator is its row in `m`. -/
@[simp]
theorem attach_m_inl (x : P) :
    (m.attach a ha hca).m (Sum.inl x) = mapDomain Sum.inl (m.m x) :=
  (rfl)

/-- The row of an attached generator is its attaching cycle. -/
@[simp]
theorem attach_m_inr (q : Q) :
    (m.attach a ha hca).m (Sum.inr q) = mapDomain Sum.inl (a q) :=
  (rfl)

/-- The free module of `m` is a differential submodule of the attached module: relabelling along
`Sum.inl` commutes with the differentials. -/
@[simp]
theorem attach_differential_mapDomain_inl (f : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m (mapDomain Sum.inl f) =
      mapDomain Sum.inl (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) :=
  rowFiniteTwistedDifferential_mapDomain Sum.inl m.m (fun _ ↦ rfl) f

/-- On the new generators the differential is the coefficient differential, plus the signed
substitution of the attaching cycles, which lies in the old free module. -/
@[simp]
theorem attach_differential_mapDomain_inr (g : Q →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m (mapDomain Sum.inr g) =
      mapDomain Sum.inr (mapRange.linearMap d g) +
        mapDomain Sum.inl (rowFiniteSignedMap (𝒜 := 𝒜) a g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ hg₁ hg₂ =>
    simp only [mapDomain_add, map_add, hg₁, hg₂]
    abel
  | single q c =>
    rw [mapDomain_single, rowFiniteTwistedDifferential_single_koszulTwist, attach_m_inr,
      rowFiniteSignedMap_apply, sum_single_index (by simp), mapDomain_smul]
    simp

/-- **The differential of the attached module is upper triangular.** On a vector with
coefficients `f` on the old generators and `g` on the new ones, it is the old differential of `f`
plus the signed substitution of the attaching cycles into `g`, on the old generators, and the
coefficient differential of `g` on the new ones. -/
theorem attach_differential_sumElim (f : P →₀ A) (g : Q →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m (sumElim f g) =
      sumElim (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f +
        rowFiniteSignedMap (𝒜 := 𝒜) a g) (mapRange.linearMap d g) := by
  rw [sumElim_eq_add, map_add, attach_differential_mapDomain_inl,
    attach_differential_mapDomain_inr, sumElim_eq_add, mapDomain_add]
  abel

/-- The differential of an attached generator is its attaching cycle. -/
@[simp]
theorem attach_differential_single_inr_one (hA : IsDGAlgebra 𝒜 d) (q : Q) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m (single (Sum.inr q) 1) =
      mapDomain Sum.inl (a q) :=
  (m.attach a ha hca).differential_single_one hA (Sum.inr q)

/-- **Attaching preserves one-sidedness**: if the rows of `m` strictly lower indices and every
attaching cycle only involves generators of index strictly below that of the new generator, then
the rows of the attached cocycle strictly lower indices. -/
theorem attach_m_eq_zero_of_le (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
    (hal : ∀ q y, indQ q ≤ ind y → a q y = 0) (z w : P ⊕ Q)
    (hzw : Sum.elim ind indQ z ≤ Sum.elim ind indQ w) : (m.attach a ha hca).m z w = 0 := by
  rcases w with y | q'
  · rcases z with x | q
    · simpa [mapDomain_apply_of_injective Sum.inl_injective] using hm x y hzw
    · simpa [mapDomain_apply_of_injective Sum.inl_injective] using hal q y hzw
  · rcases z with x | q <;> simp [mapDomain_of_notMem_range]

/-- The rows of the attached cocycle have no entries on the new generators. -/
@[simp]
theorem attach_m_apply_inr (z : P ⊕ Q) (q : Q) : (m.attach a ha hca).m z (Sum.inr q) = 0 := by
  rcases z with x | q' <;> simp [mapDomain_of_notMem_range]

/-- On the coefficients of the new generators, the differential of the attached free module is the
coefficient differential: the attaching rows only reach the old generators. -/
@[simp]
theorem attach_differential_apply_inr (v : P ⊕ Q →₀ A) (q : Q) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m v (Sum.inr q) =
      d (v (Sum.inr q)) := by
  rw [rowFiniteTwistedDifferential_apply, Finsupp.add_apply, Finsupp.sum_apply]
  simp

/-! ### The short exact sequence of the attachment -/

section Exact

variable (hA : IsDGAlgebra 𝒜 d)

/-- The inclusion of the old free module into the attached one, as a continuation cocycle. -/
noncomputable def attachInclusion : RowFiniteContinuationCocycle m (m.attach a ha hca) where
  ν x := single (Sum.inl x) 1
  mem_graded x y := by
    classical
    by_cases hxy : Sum.inl x = y
    · subst y
      simpa using SetLike.one_mem_graded 𝒜
    · simp [single_eq_of_ne (Ne.symm hxy)]
  continuation x := by
    rw [(m.attach a ha hca).differential_single_one hA, attach_m_inl]
    simp [linearCombination_apply, mapDomain]

@[simp]
theorem attachInclusion_ν (x : P) :
    (m.attachInclusion ha hca hA).ν x = single (Sum.inl x) 1 :=
  (rfl)

/-- The inclusion of the old free module is `Finsupp.mapDomain Sum.inl`. -/
@[simp]
theorem linearCombination_attachInclusion (v : P →₀ A) :
    linearCombination A (m.attachInclusion ha hca hA).ν v = mapDomain Sum.inl v := by
  simp [linearCombination_apply, mapDomain]

/-- The inclusion of the old free module is `Finsupp.mapDomain Sum.inl`, as a function. -/
theorem coe_linearCombination_attachInclusion :
    ⇑(linearCombination A (m.attachInclusion ha hca hA).ν) = mapDomain Sum.inl :=
  funext (m.linearCombination_attachInclusion ha hca hA)

/-- The projection of the attached free module onto the free module of the new generators, with
the zero cocycle, as a continuation cocycle. -/
noncomputable def attachProjection :
    RowFiniteContinuationCocycle (m.attach a ha hca) (0 : RowFiniteTwistingCocycle 𝒜 d Q indQ) where
  ν := Sum.elim 0 fun q ↦ single q 1
  mem_graded := by
    classical
    rintro (x | q) q'
    · simp [zero_mem]
    · by_cases hq : q = q'
      · subst q'
        simpa using SetLike.one_mem_graded 𝒜
      · simp [single_eq_of_ne (Ne.symm hq), zero_mem]
  continuation := by
    rintro (x | q)
    · simp
    · simp [hA.map_one_eq_zero]

@[simp]
theorem attachProjection_ν_inl (x : P) : (m.attachProjection ha hca hA).ν (Sum.inl x) = 0 :=
  (rfl)

@[simp]
theorem attachProjection_ν_inr (q : Q) :
    (m.attachProjection ha hca hA).ν (Sum.inr q) = single q 1 :=
  (rfl)

/-- The projection reads off the coefficients of the new generators. -/
@[simp]
theorem linearCombination_attachProjection_apply (v : P ⊕ Q →₀ A) (q : Q) :
    linearCombination A (m.attachProjection ha hca hA).ν v q = v (Sum.inr q) := by
  classical
  rw [linearCombination_apply, Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single (Sum.inr q)]
  · simp
  · rintro (x | q') _ hne
    · simp
    · have hne' : q' ≠ q := fun h ↦ hne (h ▸ rfl)
      simp [hne']
  · intro h
    simp [notMem_support_iff.mp h]

/-- The projection onto the new generators is onto. -/
theorem linearCombination_attachProjection_surjective :
    Function.Surjective (linearCombination A (m.attachProjection ha hca hA).ν) := by
  intro w
  refine ⟨mapDomain Sum.inr w, Finsupp.ext fun q ↦ ?_⟩
  rw [linearCombination_attachProjection_apply, mapDomain_apply_of_injective Sum.inr_injective]

/-- The inclusion of the old free module is injective. -/
theorem linearCombination_attachInclusion_injective :
    Function.Injective (linearCombination A (m.attachInclusion ha hca hA).ν) := by
  rw [coe_linearCombination_attachInclusion]
  exact mapDomain_injective Sum.inl_injective

/-- **Exactness of the attachment sequence.** A vector of the attached free module comes from the
old free module exactly when the projection onto the new generators kills it. -/
theorem exact_linearCombination_attachInclusion_attachProjection :
    Function.Exact (linearCombination A (m.attachInclusion ha hca hA).ν)
      (linearCombination A (m.attachProjection ha hca hA).ν) := by
  intro v
  rw [coe_linearCombination_attachInclusion, mem_range_mapDomain_iff _ Sum.inl_injective,
    Finsupp.ext_iff]
  simp only [linearCombination_attachProjection_apply, coe_zero, Pi.zero_apply]
  refine ⟨?_, fun h q ↦ h _ (by simp)⟩
  rintro h (x | q) hs
  · exact absurd ⟨x, rfl⟩ hs
  · exact h q

end Exact

section Maps

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {ℳ : ℤ → Submodule R M} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M} {h : IsDGAlgebra 𝒜 d}

/-- **Extending maps over attached generators.** An `A`-linear map out of the attached module,
given by the images `g` of the old generators and `c` of the new ones, commutes with the
differentials exactly when the map given by `g` does on the old module and each `c q` bounds the
image `g (a q)` of its attaching cycle. -/
theorem forall_linearCombination_attach_differential_iff (hM : IsDGLeftModule h ℳ dM)
    (g : P → M) (c : Q → M) :
    (∀ f, linearCombination A (Sum.elim g c)
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach a ha hca).m f) =
          dM (linearCombination A (Sum.elim g c) f)) ↔
      (∀ f, linearCombination A g (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
          dM (linearCombination A g f)) ∧
        ∀ q, linearCombination A g (a q) = dM (c q) := by
  rw [forall_linearCombination_rowFiniteTwistedDifferential_iff hM,
    forall_linearCombination_rowFiniteTwistedDifferential_iff hM, Sum.forall]
  simp [linearCombination_mapDomain]

end Maps

end RowFiniteTwistingCocycle

end TauCeti
