/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Continuation
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Attaching free generators to a row-finite twisted module

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)`, with free
differential graded left module `K_m = P →₀ A`. A family of new generators `q ∈ Q` of indices
`indQ q` is attached along **attaching cycles** (`RowFiniteTwistingCocycle.AttachingCycles`):
cycles `a q` of `K_m` of total degree `1 - indQ q`. The attached cocycle
`RowFiniteTwistingCocycle.attach` on `P ⊕ Q` keeps the rows of `m` and gives the new generator
`q` the row `a q`, so that its differential is `d q = a q`. The Maurer–Cartan equation of the new
row is exactly the cycle condition (`rowFiniteTwistedDifferential_eq_zero_iff`). This is the
algebraic step of Brown's construction of a semi-free resolution from the cells of a CW complex:
the cells of one dimension are attached at once, each along a cycle of the stage already built.

The attached module sits in a sequence

`0 → K_m → K_{attach} → K_0(Q) → 0`

of differential graded left modules, where `K_0(Q)` is the free module on the new generators with
the zero cocycle, carrying the coefficient differential alone. The inclusion
(`RowFiniteTwistingCocycle.attachInclusion`) and the projection onto the new coordinates
(`RowFiniteTwistingCocycle.attachProjection`) are continuation cocycles, hence chain maps; the
inclusion is injective, its image is the kernel of the projection
(`RowFiniteTwistingCocycle.exact_linearCombination_attachInclusion_attachProjection`), and the
projection is onto. So the quotient by the old generators is a direct sum of shifted copies of the
algebra, one for each new generator, as for the relative chains of a CW pair.

Maps out of the attached module have the universal property of a cell attachment. Generator images
`f` for `m` in a differential graded left module `(ℳ, dM)` extend to the attached cocycle exactly
by choosing, for each new generator `q`, an element `c q` of degree `-indQ q` with
`dM (c q) = f (a q)` (`RowFiniteTwistingCocycle.GeneratorMap.attach`,
`RowFiniteTwistingCocycle.GeneratorMap.eq_attach`). In particular `f` extends exactly when the
image of every attaching cycle is the differential of an element of the degree of its new
generator (`RowFiniteTwistingCocycle.GeneratorMap.exists_extension_iff`).

## Main definitions and results

* `RowFiniteTwistingCocycle.AttachingCycles` and `RowFiniteTwistingCocycle.attach`.
* `RowFiniteTwistingCocycle.attach_oneSided`: attaching along cycles of lower index preserves
  one-sidedness.
* `RowFiniteTwistingCocycle.attachInclusion`, `RowFiniteTwistingCocycle.attachProjection` and
  `RowFiniteTwistingCocycle.exact_linearCombination_attachInclusion_attachProjection`: the short
  exact sequence of the attachment.
* `RowFiniteTwistingCocycle.GeneratorMap.attach`, `RowFiniteTwistingCocycle.GeneratorMap.eq_attach`
  and `RowFiniteTwistingCocycle.GeneratorMap.exists_extension_iff`: extending generator images over
  the new generators.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6.
-/

public noncomputable section

namespace TauCeti

universe uR uA uM uP uQ

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP} {Q : Type uQ}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ} {indQ : Q → ℤ}

namespace RowFiniteTwistingCocycle

/-- Attaching cycles for new generators `q ∈ Q` of indices `indQ q`: for each `q`, a cycle of the
free module `K_m` of total degree `1 - indQ q`, the prescribed differential of `q`. -/
structure AttachingCycles (m : RowFiniteTwistingCocycle 𝒜 d P ind) (Q : Type uQ)
    (indQ : Q → ℤ) where
  /-- The row of each new generator: its differential, a vector of the old free module. -/
  row : Q → P →₀ A
  /-- The row of a new generator has the shifted degree of a twisting row. -/
  mem_graded : ∀ q x, row q x ∈ 𝒜 (ind x - indQ q + 1)
  /-- Each row is a cycle of the old free module. -/
  differential_row : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m (row q) = 0

@[ext]
theorem AttachingCycles.ext {m : RowFiniteTwistingCocycle 𝒜 d P ind}
    {α β : m.AttachingCycles Q indQ} (h : ∀ q x, α.row q x = β.row q x) : α = β := by
  cases α
  cases β
  congr
  funext q
  exact Finsupp.ext (h q)

variable (m : RowFiniteTwistingCocycle 𝒜 d P ind) (α : m.AttachingCycles Q indQ)

omit [GradedAlgebra 𝒜] in
/-- Maurer–Cartan rows on `P` remain Maurer–Cartan rows after the old generators are included
into `P ⊕ Q`, for any rows of the new generators. -/
private theorem twisting_mapDomain_inl (rows : P ⊕ Q → P ⊕ Q →₀ A)
    (hrows : ∀ y, rows (Sum.inl y) = (m.m y).mapDomain Sum.inl) {i : ℤ} {r : P →₀ A}
    (hr : Finsupp.mapRange.linearMap d r =
      r.sum fun y a ↦ (i - ind y).negOnePow • (a • m.m y)) :
    Finsupp.mapRange.linearMap d (r.mapDomain Sum.inl) =
      (r.mapDomain Sum.inl).sum fun y a ↦
        (i - Sum.elim ind indQ y).negOnePow • (a • rows y) := by
  rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective, Finsupp.mapRange.linearMap_apply,
    ← Finsupp.mapDomain_mapRange _ _ _ _ (map_add d), ← Finsupp.mapRange.linearMap_apply (R := R),
    hr, Finsupp.mapDomain_sum]
  simp only [Sum.elim_inl, hrows, Finsupp.mapDomain_smul]

/-- The cocycle obtained from `m` by attaching the new generators `q ∈ Q`, of indices `indQ q`,
along the attaching cycles `α`: the old generators keep their rows, and the differential of `q` is
`α.row q`. -/
def attach : RowFiniteTwistingCocycle 𝒜 d (P ⊕ Q) (Sum.elim ind indQ) where
  m := Sum.elim (fun x ↦ (m.m x).mapDomain Sum.inl) fun q ↦ (α.row q).mapDomain Sum.inl
  mem_graded := by
    rintro (x | q) (y | q')
    · simpa [Finsupp.mapDomain_apply_of_injective Sum.inl_injective] using m.mem_graded x y
    · simp [Finsupp.mapDomain_of_notMem_range, zero_mem]
    · simpa [Finsupp.mapDomain_apply_of_injective Sum.inl_injective] using α.mem_graded q y
    · simp [Finsupp.mapDomain_of_notMem_range, zero_mem]
  twisting := by
    rintro (x | q)
    · exact m.twisting_mapDomain_inl _ (fun _ ↦ rfl) (m.twisting x)
    · exact m.twisting_mapDomain_inl _ (fun _ ↦ rfl)
        ((rowFiniteTwistedDifferential_eq_zero_iff m.m (α.mem_graded q)).mp (α.differential_row q))

@[simp]
theorem attach_m_inl (x : P) : (m.attach α).m (Sum.inl x) = (m.m x).mapDomain Sum.inl :=
  (rfl)

@[simp]
theorem attach_m_inr (q : Q) : (m.attach α).m (Sum.inr q) = (α.row q).mapDomain Sum.inl :=
  (rfl)

/-- The rows of the attached cocycle have no entries on the new generators. -/
@[simp]
theorem attach_m_apply_inr (s : P ⊕ Q) (q : Q) : (m.attach α).m s (Sum.inr q) = 0 := by
  rcases s with x | q' <;> simp [Finsupp.mapDomain_of_notMem_range]

/-- Attaching along cycles carried by generators of lower index preserves one-sidedness. -/
theorem attach_oneSided (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
    (hα : ∀ q x, indQ q ≤ ind x → α.row q x = 0) :
    ∀ s t, Sum.elim ind indQ s ≤ Sum.elim ind indQ t → (m.attach α).m s t = 0 := by
  rintro (x | q) (y | q') h
  · simpa [Finsupp.mapDomain_apply_of_injective Sum.inl_injective] using hm x y h
  · simp [Finsupp.mapDomain_of_notMem_range]
  · simpa [Finsupp.mapDomain_apply_of_injective Sum.inl_injective] using hα q y h
  · simp [Finsupp.mapDomain_of_notMem_range]

/-! ### The short exact sequence of the attachment -/

variable (hA : IsDGAlgebra 𝒜 d)

/-- The inclusion of the old free module into the attached one, as a continuation cocycle. -/
def attachInclusion : RowFiniteContinuationCocycle m (m.attach α) where
  ν x := Finsupp.single (Sum.inl x) 1
  mem_graded x y := by
    classical
    by_cases hxy : Sum.inl x = y
    · subst y
      simpa using SetLike.one_mem_graded 𝒜
    · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]
  continuation x := by
    rw [(m.attach α).differential_single_one hA, attach_m_inl,
      Finsupp.linearCombination_single_one_eq_mapDomain]

@[simp]
theorem attachInclusion_ν (x : P) :
    (m.attachInclusion α hA).ν x = Finsupp.single (Sum.inl x) 1 :=
  (rfl)

/-- The inclusion of the old free module is `Finsupp.mapDomain Sum.inl`. -/
@[simp]
theorem linearCombination_attachInclusion (v : P →₀ A) :
    Finsupp.linearCombination A (m.attachInclusion α hA).ν v = v.mapDomain Sum.inl :=
  Finsupp.linearCombination_single_one_eq_mapDomain Sum.inl v

/-- The inclusion of the old free module is `Finsupp.mapDomain Sum.inl`, as a function. -/
theorem coe_linearCombination_attachInclusion :
    ⇑(Finsupp.linearCombination A (m.attachInclusion α hA).ν) = Finsupp.mapDomain Sum.inl :=
  funext (m.linearCombination_attachInclusion α hA)

include hA in
/-- The inclusion of the old free module commutes with the differentials. -/
theorem rowFiniteTwistedDifferential_attach_mapDomain_inl (v : P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach α).m (v.mapDomain Sum.inl) =
      (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m v).mapDomain Sum.inl := by
  simpa using (m.attachInclusion α hA).linearCombination_differential hA v

/-- The projection of the attached free module onto the free module of the new generators, with
the zero cocycle, as a continuation cocycle. -/
def attachProjection :
    RowFiniteContinuationCocycle (m.attach α) (0 : RowFiniteTwistingCocycle 𝒜 d Q indQ) where
  ν := Sum.elim 0 fun q ↦ Finsupp.single q 1
  mem_graded := by
    classical
    rintro (x | q) q'
    · simp [zero_mem]
    · by_cases hq : q = q'
      · subst q'
        simpa using SetLike.one_mem_graded 𝒜
      · simp [Finsupp.single_eq_of_ne (Ne.symm hq), zero_mem]
  continuation := by
    rintro (x | q)
    · simp
    · simp [hA.map_one_eq_zero]

@[simp]
theorem attachProjection_ν_inl (x : P) : (m.attachProjection α hA).ν (Sum.inl x) = 0 :=
  (rfl)

@[simp]
theorem attachProjection_ν_inr (q : Q) :
    (m.attachProjection α hA).ν (Sum.inr q) = Finsupp.single q 1 :=
  (rfl)

/-- The projection reads off the coefficients of the new generators. -/
@[simp]
theorem linearCombination_attachProjection_apply (v : P ⊕ Q →₀ A) (q : Q) :
    Finsupp.linearCombination A (m.attachProjection α hA).ν v q = v (Sum.inr q) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
  rw [Finset.sum_eq_single (Sum.inr q)]
  · simp
  · rintro (x | q') _ hne
    · simp
    · simp [show q' ≠ q from fun h ↦ hne (h ▸ rfl)]
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

include hA in
/-- On the coefficients of the new generators, the differential of the attached free module is the
coefficient differential: the attaching rows only reach the old generators. -/
theorem rowFiniteTwistedDifferential_attach_apply_inr (v : P ⊕ Q →₀ A) (q : Q) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (m.attach α).m v (Sum.inr q) =
      d (v (Sum.inr q)) := by
  have h := congrArg (· q) ((m.attachProjection α hA).linearCombination_differential hA v)
  simpa using h.symm

/-- The projection onto the new generators is onto. -/
theorem linearCombination_attachProjection_surjective :
    Function.Surjective (Finsupp.linearCombination A (m.attachProjection α hA).ν) := by
  intro w
  refine ⟨w.mapDomain Sum.inr, Finsupp.ext fun q ↦ ?_⟩
  rw [linearCombination_attachProjection_apply,
    Finsupp.mapDomain_apply_of_injective Sum.inr_injective]

/-- The inclusion of the old free module is injective. -/
theorem linearCombination_attachInclusion_injective :
    Function.Injective (Finsupp.linearCombination A (m.attachInclusion α hA).ν) := by
  rw [coe_linearCombination_attachInclusion]
  exact Finsupp.mapDomain_injective Sum.inl_injective

/-- **Exactness of the attachment sequence.** A vector of the attached free module comes from the
old free module exactly when the projection onto the new generators kills it. -/
theorem exact_linearCombination_attachInclusion_attachProjection :
    Function.Exact (Finsupp.linearCombination A (m.attachInclusion α hA).ν)
      (Finsupp.linearCombination A (m.attachProjection α hA).ν) := by
  intro v
  rw [coe_linearCombination_attachInclusion, Finsupp.mem_range_mapDomain_iff _ Sum.inl_injective,
    Finsupp.ext_iff]
  simp only [linearCombination_attachProjection_apply, Finsupp.coe_zero, Pi.zero_apply]
  refine ⟨?_, fun h q ↦ h _ (by simp)⟩
  rintro h (x | q) hs
  · exact absurd ⟨x, rfl⟩ hs
  · exact h q

/-! ### Extending generator images over the new generators -/

namespace GeneratorMap

variable {m α} [AddCommGroup M] [Module R M] [Module A M] {ℳ : ℤ → Submodule R M}
  {dM : M →ₗ[R] M} (f : m.GeneratorMap ℳ dM)

/-- Extend generator images over the attached generators, sending the new generator `q` to an
element `c q` of its degree whose differential is the image of the attaching cycle of `q`. -/
def attach (c : Q → M) (hc : ∀ q, c q ∈ ℳ (-indQ q))
    (hdc : ∀ q, dM (c q) = Finsupp.linearCombination A f.image (α.row q)) :
    (m.attach α).GeneratorMap ℳ dM where
  image := Sum.elim f.image c
  mem_graded := by
    rintro (x | q)
    · exact f.mem_graded x
    · exact hc q
  differential_image := by
    rintro (x | q)
    · simpa using f.differential_image x
    · simpa using hdc q

@[simp]
theorem attach_image (c : Q → M) (hc : ∀ q, c q ∈ ℳ (-indQ q))
    (hdc : ∀ q, dM (c q) = Finsupp.linearCombination A f.image (α.row q)) :
    (f.attach c hc hdc).image = Sum.elim f.image c :=
  (rfl)

/-- On the old free module, the extended map is the original one. -/
theorem linearCombination_attach_mapDomain_inl (c : Q → M) (hc : ∀ q, c q ∈ ℳ (-indQ q))
    (hdc : ∀ q, dM (c q) = Finsupp.linearCombination A f.image (α.row q)) (v : P →₀ A) :
    Finsupp.linearCombination A (f.attach c hc hdc).image (v.mapDomain Sum.inl) =
      Finsupp.linearCombination A f.image v := by
  simp

/-- Generator images for the attached cocycle which agree with `f` on the old generators send each
new generator to an element whose differential is the image of its attaching cycle under `f`. -/
theorem differential_image_inr (g : (m.attach α).GeneratorMap ℳ dM)
    (hg : ∀ x, g.image (Sum.inl x) = f.image x) (q : Q) :
    dM (g.image (Sum.inr q)) = Finsupp.linearCombination A f.image (α.row q) := by
  rw [g.differential_image (Sum.inr q), attach_m_inr, Finsupp.linearCombination_mapDomain]
  exact congrArg (Finsupp.linearCombination A · (α.row q)) (funext hg)

/-- **Uniqueness of extensions.** Generator images for the attached cocycle which agree with `f`
on the old generators are the extension of `f` by their values on the new generators. -/
theorem eq_attach (g : (m.attach α).GeneratorMap ℳ dM)
    (hg : ∀ x, g.image (Sum.inl x) = f.image x) :
    g = f.attach (fun q ↦ g.image (Sum.inr q)) (fun q ↦ g.mem_graded (Sum.inr q))
      (f.differential_image_inr g hg) := by
  ext (x | q)
  · exact hg x
  · rfl

/-- **The obstruction to extending over the new generators.** Generator images for `m` extend to
the attached cocycle exactly when the image of every attaching cycle is the differential of an
element of the degree of its new generator. -/
theorem exists_extension_iff :
    (∃ g : (m.attach α).GeneratorMap ℳ dM, ∀ x, g.image (Sum.inl x) = f.image x) ↔
      ∀ q, ∃ c ∈ ℳ (-indQ q), dM c = Finsupp.linearCombination A f.image (α.row q) := by
  constructor
  · rintro ⟨g, hg⟩ q
    exact ⟨g.image (Sum.inr q), g.mem_graded (Sum.inr q), f.differential_image_inr g hg q⟩
  · intro h
    choose c hc hdc using h
    exact ⟨f.attach c hc hdc, fun _ ↦ rfl⟩

end GeneratorMap

end RowFiniteTwistingCocycle

end TauCeti
