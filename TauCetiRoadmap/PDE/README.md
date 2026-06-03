# Roadmap: partial differential equations

Mathlib master already carries a deep analysis stack: distributions, the Schwartz space,
the full Fourier transform with inversion and Plancherel, convolution and mollifiers, the
Gagliardo–Nirenberg–Sobolev inequality, **Bessel-potential Sobolev spaces**, the
Laplacian on inner-product spaces, harmonic-function theory, **Lax–Milgram**, the
**Fredholm alternative for compact operators**, and Picard–Lindelöf for ODEs. What is
still missing is the **PDE theory built on top**: weak-derivative Sobolev spaces on a
domain with their embedding/trace/compactness package, maximum principles, the
harmonic-analysis estimates (maximal function, Calderón–Zygmund, interpolation), and the
existence-and-regularity theorems for elliptic and parabolic equations.

The bar for "done": a researcher in elliptic or parabolic PDE looks at this material and
says *"the prerequisites are all here, in reusable form, and I can start my work."*

## The end goal (v1)

For a **bounded open `Ω ⊆ ℝⁿ`** and a **uniformly elliptic, divergence-form** operator
`L u = -∂ⱼ(aⁱʲ ∂ᵢ u) + bⁱ ∂ᵢ u + c u` with bounded measurable coefficients, deliver the
**three pillars** for the Dirichlet problem `L u = f` in `Ω`, `u = g` on `∂Ω`:

1. **Existence and uniqueness** of a weak solution in `H¹(Ω)` (energy method: Gårding's
   inequality plus Lax–Milgram; the Fredholm alternative when coercivity fails).
2. **Regularity:** weak solutions are locally Hölder continuous
   (**De Giorgi–Nash–Moser**, the bounded-measurable-coefficient case), and smooth when
   the coefficients and data are smooth (interior `Hᵏ`/Schauder estimates).
3. **The maximum principle** (weak and strong) and the **Harnack inequality** for the
   homogeneous equation, with the classical potential theory (mean-value property,
   Newtonian potential, Perron's method) as the constant-coefficient template.

```lean
-- the shape we are building toward (state in Targets.lean as the supporting types land):
-- variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hb : IsBounded Ω)
--
-- the energy bilinear form of L, weak (distributional) formulation:
-- def energyForm (a : Ω → Matrix (Fin n) (Fin n) ℝ) (b : Ω → ...) (c : Ω → ℝ) :
--     (Wkp 1 2 Ω) → (Wkp 1 2 Ω) → ℝ
--
-- existence/uniqueness of the weak solution (Dirichlet, homogeneous BC), via Lax–Milgram:
-- theorem exists_unique_weakSolution (helliptic : UniformlyElliptic λ Λ a) (hcoercive : ...)
--     (f : Lp ℝ 2 (volume.restrict Ω)) :
--     ∃! u : Wkp0 1 2 Ω, ∀ v : Wkp0 1 2 Ω, energyForm a b c u v = ∫ x in Ω, f x * v x
--
-- De Giorgi–Nash–Moser interior regularity of the weak solution:
-- theorem weakSolution_holderOn (hu : IsWeakSolution L u f) (hcompact : K ⊆ Ω) (hK : IsCompact K) :
--     ∃ α ∈ Set.Ioc (0:ℝ) 1, HolderOnWith C α u K
```

## Standing hypotheses (spell them out; never bundle)

PDE theory is **example-driven and hypothesis-sensitive**: the same theorem is true in
many incomparable forms, and the art is in tracking exactly which structure each proof
needs. Separate typeclass assumptions let every result land in its correct generality, so
there will be **no** monolithic `EllipticPDE` class. State each of these as a named,
separate hypothesis:

- **Domain regularity.** Most of the theory needs a bounded open `Ω`. *Trace*,
  *extension*, and *Rellich–Kondrachov* additionally need boundary regularity
  (Lipschitz, or `C¹`, or the cone/segment condition). Carry the boundary hypothesis
  explicitly: interior estimates do **not** need it, global ones do.
- **Uniform ellipticity** with *explicit* constants `0 < λ ≤ Λ`:
  `λ‖ξ‖² ≤ aⁱʲ(x) ξᵢ ξⱼ ≤ Λ‖ξ‖²`. Almost every estimate's constant depends on `λ, Λ, n`
  and the domain only, so make that dependence visible, not hidden in a `∃ C`.
- **Coefficient regularity is a *dial*, and it selects the theory:**
  - *bounded measurable* `aⁱʲ` gives **divergence form**, **weak** solutions, De Giorgi–Nash–Moser;
  - *Hölder* `aⁱʲ ∈ C^{0,α}` gives **Schauder** `C^{2,α}` estimates (classical solutions);
  - *continuous / VMO* `aⁱʲ` gives **Calderón–Zygmund** `W^{2,p}` estimates (strong solutions).
  Keep these lanes distinct; do not state one result and silently assume the regularity of
  another.

## Getting the statements right

A few cross-cutting rules for the *shape* of a PDE statement: which hypotheses it carries
and which notion it names. These recur across the lanes below, and getting them right at
statement time is what keeps the formalized API reusable.

- **Name the solution concept.** State whether a theorem is about *classical* (`C²`, the
  PDE holds pointwise), *strong* (`W^{2,p}`, a.e.), or *weak* (`H¹`, against test
  functions) solutions, and which of these it assumes versus produces. The regularity lane
  is exactly the passage from weak to classical.
- **Build domain Sobolev spaces from weak derivatives, then connect them to the Fourier
  scale.** The PDE workhorse is `W^{k,p}(Ω)` on a domain via weak derivatives; build it,
  then *prove* it agrees with Mathlib's Fourier/Bessel-potential spaces
  (`TemperedDistribution.memSobolev`) on `ℝⁿ` in the range where they coincide
  (`1 < p < ∞`, integer `s`; Calderón). Don't reuse the Bessel definition as the domain
  theory: it is a whole-space notion and the two scales genuinely differ at `p = 1, ∞`.
- **Carry Poincaré's normalization.** `‖u‖ ≤ C‖∇u‖` holds on `W^{1,p}_0(Ω)` (zero trace)
  or modulo constants (Poincaré–Wirtinger, zero mean), for `Ω` bounded (or of finite
  measure, or bounded in one direction). State that side condition explicitly; it is the
  load-bearing hypothesis (the inequality fails outright on `ℝⁿ`).
- **Pick the Sobolev-embedding regime by exponent.** Subcritical `p < n` gives
  `W^{1,p} ↪ L^{p*}`, `p* = np/(n−p)` (consume Gagliardo–Nirenberg–Sobolev); supercritical
  `p > n` gives Hölder `C^{0,1−n/p}` (Morrey); the borderline `p = n` gives
  BMO/exponential integrability (Trudinger–Moser), not `L^∞`. State the regime you mean
  rather than a single catch-all embedding.
- **Use weak compactness for existence; reserve norm compactness for Rellich.** Existence
  arguments run on *weak* sequential compactness of bounded sets in a reflexive space
  (Banach–Alaoglu / `WeakDual`). Norm compactness comes from one place,
  **Rellich–Kondrachov**: `W^{1,p}(Ω) ↪↪ L^p(Ω)` is compact for bounded `Ω`, the embedding
  that powers the Fredholm alternative and the eigenvalue expansions.
- **State maximum principles with their hypotheses.** The weak maximum principle for
  `Lu = -∂ⱼ(aⁱʲ∂ᵢu) + cu` needs `c ≥ 0` (or `Lu ≤ 0` with the right structure); the strong
  principle additionally needs `Ω` connected and rests on the **Hopf boundary-point
  lemma**; Harnack is for nonnegative solutions. Make each of these a named hypothesis.
- **Fix the Laplacian sign and Fourier convention once.** Pin the sign of `Δ` (Mathlib's
  convention in `InnerProductSpace/Laplacian.lean`), and note Mathlib's Bessel potential is
  `(1 − (2π)⁻² Δ)^{s/2}`, not `(1 − Δ)^{s/2}`, because of the `2π` in its Fourier
  transform. This is harmless when *defining* the spaces, but a mismatch in an estimate is
  a real error.
- **Keep divergence and non-divergence form apart.** De Giorgi–Nash–Moser is
  divergence-form/weak; its non-divergence-form counterpart is **Krylov–Safonov** (`Lᵖ`
  viscosity / `W^{2,p}` strong). They are different theories, so don't transfer one's
  conclusion under the other's hypotheses.

## Inventory: what Mathlib master gives us (consume)

- **Distributions & test functions** in `Mathlib/Analysis/Distribution/*`:
  `Distribution` (`𝓓'(Ω, F)`, general `F`-valued, finite-dim domain), `TestFunction`
  (`𝓓(Ω)`), `ContDiffMapSupportedIn`, `TemperedDistribution` (`𝓢'`), `SchwartzSpace`
  (`𝓢`), `FourierSchwartz`, `FourierMultiplier`, `TemperateGrowth`, and the distributional
  `DerivNotation`. This is a *substantial* head start: the test-function/distribution
  pairing is already done.
- **Sobolev (Bessel potential)** in `Mathlib/Analysis/Distribution/Sobolev.lean`:
  `besselPotential`, `memSobolev` (the `H^{s,p}` scale), `memSobolev_two_iff_fourier`,
  and the operator actions `MemSobolev.lineDerivOp`, `MemSobolev.laplacian`. Reconcile
  with (do not duplicate) the weak-derivative spaces you build.
- **The Sobolev inequality** in `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`:
  `eLpNorm_le_eLpNorm_fderiv_of_eq` / `…_of_le` (Gagliardo–Nirenberg–Sobolev, van Doorn–
  Macbeth). The subcritical embedding estimate, already proved; *consume it directly* for
  the `p < n` case.
- **Fourier analysis** in `Mathlib/Analysis/Fourier/*`: `FourierTransform`, `Inversion`,
  `LpSpace` (Plancherel/Hausdorff–Young flavour), `FourierTransformDeriv`,
  `RiemannLebesgueLemma`, `PoissonSummation`, `Convolution`.
- **Convolution & mollifiers** in `Mathlib/Analysis/Convolution.lean` and
  `Mathlib/Analysis/Calculus/BumpFunction/*` (`ContDiffBump`, `Convolution`), the
  approximate-identity machinery for density and smoothing.
- **The Laplacian & harmonic functions** in
  `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` (`Δ` on `E → F`, real f.d. inner
  product space), `…/InnerProductSpace/Harmonic/*` (`HarmonicAt`, `HarmonicOnNhd`, the
  algebra of harmonic functions), and `Mathlib/Analysis/Complex/Harmonic/*` (mean-value
  property, Liouville, Poisson kernel, harmonic ⇔ locally `Re` of analytic). The `n = 2`
  potential theory is essentially *there*.
- **Hilbert-space machinery for the energy method** in
  `Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean` (`IsCoercive`,
  `continuousLinearEquivOfBilin`, i.e. **Lax–Milgram itself**),
  `…/InnerProductSpace/Dual.lean` (**Fréchet–Riesz** `toDual`),
  `…/InnerProductSpace/Adjoint.lean`, `…/InnerProductSpace/Projection.lean`.
- **Spectral theory** in `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`: the spectral
  theorem for symmetric operators (finite-dim diagonalization; for **compact** operators,
  `finite_dimensional_eigenspace` and `eq_zero_of_forall_hasEigenvalue_eq_zero`), and
  `Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean` (the **Fredholm
  alternative**). The eigenvalue/eigenfunction-expansion lane builds directly on these.
- **Functional-analysis backbone:** Hahn–Banach
  (`Mathlib/Analysis/Normed/Module/HahnBanach.lean`), Banach–Steinhaus
  (`…/Normed/Operator/BanachSteinhaus.lean`), open mapping / closed graph, weak topologies
  (`…/Normed/Module/WeakDual.lean`, `…/LocallyConvex/WeakDual.lean`), Arzelà–Ascoli
  (`Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`).
- **Integration:** the Bochner integral (`Mathlib/MeasureTheory/Integral/Bochner/*`, the
  vector-valued integral the parabolic lane needs), `Lp`/`eLpNorm`, Hölder & Minkowski,
  conditional expectation, Besicovitch/Vitali covering
  (`Mathlib/MeasureTheory/Covering/*`).
- **ODEs** in `Mathlib/Analysis/ODE/*`: Picard–Lindelöf (`ExistUnique`), Grönwall. The
  Galerkin/method-of-lines and the characteristic-curve lanes consume these.

## Inventory: what is missing (build here)

- **Weak-derivative Sobolev spaces `W^{k,p}(Ω)`** on a domain (distinct from the
  Bessel-potential scale): weak derivatives, completeness, `W^{k,p}_0` as the
  `C_c^∞`-closure, Meyers–Serrin `H = W` density, and the agreement theorem with the
  Fourier `H^{s,p}` on `ℝⁿ`.
- **The embedding/trace/compactness package:** Morrey `C^{0,α}` embedding (`p > n`), the
  borderline `p = n` case, **Poincaré** and Poincaré–Wirtinger, the **trace operator** on
  `∂Ω` and its kernel `= W^{1,p}_0`, the **extension operator**, and
  **Rellich–Kondrachov** compactness.
- **Hölder spaces `C^{k,α}`** as Banach spaces (for Schauder), and the Campanato/Morrey
  space characterization.
- **Harmonic-analysis estimates:** the **Hardy–Littlewood maximal function** and its weak
  `(1,1)` / strong `(p,p)` bounds (vendor from the Carleson project), the
  **Calderón–Zygmund decomposition**, **singular integral operators** with the CZ kernel
  bounds, the **Mihlin–Hörmander multiplier theorem**, and **interpolation**
  (Riesz–Thorin and **Marcinkiewicz**, *neither* of which is in Mathlib). BMO and
  John–Nirenberg as a sub-lane.
- **Maximum principles & potential theory:** weak and strong maximum principles, the
  **Hopf lemma**, comparison principles, the **Harnack inequality**, the Newtonian
  potential / fundamental solution of `Δ`, the Green's function, the Poisson kernel on
  `ℝⁿ` (the half-space and the ball), and **Perron's method** for the Dirichlet problem.
- **Elliptic existence & regularity:** the energy/weak formulation and Gårding's
  inequality (then Lax–Milgram, *consumed*); interior and boundary `Hᵏ`/`Lᵖ` estimates
  (difference quotients, Calderón–Zygmund); **Schauder** `C^{2,α}` estimates;
  **De Giorgi–Nash–Moser**; eigenvalues of `−Δ` via the compact-self-adjoint spectral
  theorem.
- **Parabolic & evolution equations:** Bochner spaces `L²(0,T;H)`, the Gelfand triple
  `V ↪ H ↪ V*`, the **Galerkin method**, existence for linear parabolic equations, the
  parabolic maximum principle, the **heat semigroup** and **Hille–Yosida**.

---

## The build, in lanes

Each lane is self-contained analysis worth having on its own; the ordering below is the
dependency order, not a strict schedule, and the lanes are deliberately parallelizable.
As a lane makes the next one's *types* expressible in `TauCeti/`, state those milestones
in `Targets.lean` (with `sorry`, which is human-owned roadmap territory) and hand them to
the AIs to discharge.

### Lane A: function spaces on a domain (the universal prerequisite)

Almost everything downstream waits on this, so do it first and do it right.

1. **`W^{k,p}(Ω)` via weak derivatives.** Define the weak (distributional) derivative of a
   locally integrable function, `W^{k,p}(Ω)` with its norm, and prove **completeness**.
   Build on Mathlib's `Distribution`/`TestFunction` pairing so the definition is the
   honest one (`∫ u ∂^α φ = (−1)^{|α|} ∫ (D^α u) φ` for all test `φ`).
2. **Density and `W^{k,p}_0`.** Mollification (consume `BumpFunction/Convolution`) gives
   `C^∞ ∩ W^{k,p}` dense (**Meyers–Serrin**, `H = W`); define `W^{k,p}_0(Ω)` as the
   `C_c^∞(Ω)`-closure. ⚠ `H = W` needs no boundary regularity; `W^{k,p}_0 = W^{k,p}` for
   `Ω = ℝⁿ` but **not** for bounded `Ω`.
3. **Reconcile with Mathlib's Bessel-potential scale.** Prove `W^{k,2}(ℝⁿ) = H^{k,2}(ℝⁿ)`
   (and the `1<p<∞` integer-order Calderón agreement) so the two definitions are known to
   coincide where both make sense; *do not* leave them as unrelated theories.
4. **Embeddings.** *Consume* Gagliardo–Nirenberg–Sobolev for `p<n`; **build** the Morrey
   embedding `W^{1,p}(Ω) ↪ C^{0,1−n/p}(Ω)` for `p>n`, and state (then prove) the
   borderline `p=n`.
5. **Poincaré** on `W^{1,p}_0(Ω)` (bounded `Ω`) and **Poincaré–Wirtinger** (zero mean),
   with explicit constant dependence.
6. **Trace, extension, Rellich.** The **trace operator** `W^{1,p}(Ω) → L^p(∂Ω)` with
   `ker = W^{1,p}_0` (Lipschitz `∂Ω`), an **extension operator** `W^{1,p}(Ω) → W^{1,p}(ℝⁿ)`,
   and **Rellich–Kondrachov**: `W^{1,p}(Ω) ↪↪ L^p(Ω)` **compact** for bounded `Ω` (via
   Fréchet–Kolmogorov / Arzelà–Ascoli). This is the keystone for Lane D and the
   eigenvalue theory.
7. **Hölder spaces `C^{k,α}(Ω)`** as Banach spaces, the target spaces for Schauder.

### Lane B: harmonic-analysis estimates

The estimate engine for Calderón–Zygmund regularity and Schauder. Vendor heavily from the
**Carleson project**, which already has the maximal function and covering machinery.

8.  **Hardy–Littlewood maximal function** `Mf` and the **maximal inequality**: weak
    `(1,1)` (via Vitali, consuming `MeasureTheory/Covering/*`) and strong `(p,p)` for
    `p>1`, with the Lebesgue differentiation theorem as a corollary.
9.  **Interpolation.** **Marcinkiewicz** (real, weak-type to strong-type) and
    **Riesz–Thorin** (complex). *Neither is in Mathlib*; both are foundational and
    reusable far beyond PDE.
10. **Calderón–Zygmund.** The **CZ decomposition** of an `L¹` function at height `t`; the
    **CZ singular integral operators** (standard kernel bounds) bounded on `Lᵖ`, `1<p<∞`,
    and weak-`(1,1)`; the **Mihlin–Hörmander multiplier theorem** (consume Mathlib's
    `FourierMultiplier`). ⚠ A CZ operator is **not** bounded on `L¹` or `L^∞`; the
    endpoints are weak-`(1,1)` and `L^∞ → BMO`, and stating an `L¹`/`L^∞` bound is the
    classic error.
11. **BMO and John–Nirenberg** (sub-lane): `BMO(ℝⁿ)`, the John–Nirenberg inequality, and
    the `L^∞ → BMO` endpoint for CZ operators.

### Lane C: maximum principles and potential theory

The classical, constant-coefficient theory; the cleanest lane and a good early win, with
much of the `n=2` case already in Mathlib's complex harmonic-function files.

12. **Mean-value property and smoothness of harmonic functions** on `ℝⁿ` (consume the
    `n=2` complex theory; generalize the mean-value characterization to `ℝⁿ`).
13. **The weak and strong maximum principles** for `Δ` and then for general elliptic `L`
    (sign condition `c ≥ 0`); the **Hopf boundary-point lemma**; the comparison principle.
14. **The Harnack inequality** for nonnegative harmonic functions, then for general
    elliptic `L` (this feeds De Giorgi–Nash–Moser in Lane E).
15. **Fundamental solution / Newtonian potential** of `Δ` on `ℝⁿ`, the **Green's
    function** and **Poisson kernel** on the ball/half-space, and **Perron's method**:
    existence for the Dirichlet problem `Δu = 0` in `Ω`, `u = g` on `∂Ω`, via subharmonic
    barriers. ⚠ Perron yields a harmonic function for *any* bounded `Ω`; **boundary
    attainment** of `g` is a separate statement needing a **barrier** at each boundary
    point (regular boundary points).

### Lane D: linear elliptic existence (the energy method)

The shortest path to a genuine PDE existence theorem, because Lax–Milgram is *already in
Mathlib*. This lane mostly assembles Lane A and Mathlib.

16. **Weak formulation.** The energy bilinear form `a(u,v) = ∫ aⁱʲ ∂ᵢu ∂ⱼv + …` on
    `H¹_0(Ω) × H¹_0(Ω)`; boundedness; **Gårding's inequality**
    `a(u,u) ≥ α‖u‖²_{H¹} − β‖u‖²_{L²}` from uniform ellipticity.
17. **Existence & uniqueness (coercive case).** When `a` is coercive, *consume* Lax–Milgram
    (`continuousLinearEquivOfBilin`) for the unique weak solution of the Dirichlet problem.
    This is the first end-to-end PDE theorem and should land early.
18. **The Fredholm alternative (non-coercive case).** Using Rellich (Lane A.6) to make the
    resolvent compact, *consume* `FredholmAlternative` to get the
    "either-unique-solution-or-finite-dim-kernel" dichotomy for `Lu = f`.
19. **Spectrum of `−Δ`.** The Dirichlet eigenvalues/eigenfunctions of `−Δ` on a bounded
    `Ω`: a compact self-adjoint inverse (Rellich plus Lax–Milgram), then the eigenfunction
    basis from `InnerProductSpace/Spectrum`. The model **Sturm–Liouville** /
    separation-of-variables payoff.

### Lane E: elliptic regularity

The deepest lane, and the route from weak to classical solutions; it is the heart of the
classical elliptic theory (Schauder, De Giorgi–Nash–Moser).

20. **Interior `H²`/`Hᵏ` estimates** via difference quotients: a weak `H¹` solution with
    `L²` data is locally `H²`, bootstrapping to `C^∞` for smooth coefficients and data.
21. **Calderón–Zygmund `W^{2,p}` estimates** for strong solutions (consume Lane B): the
    `Lᵖ` theory of `D²u` for `Δu = f`, then variable continuous/VMO coefficients.
22. **Schauder estimates.** Interior and global `C^{2,α}` estimates for `C^{0,α}`
    coefficients (Lane B / Campanato approach), giving classical solvability of the
    Dirichlet problem in `C^{2,α}`.
23. **De Giorgi–Nash–Moser.** Local boundedness and **Hölder continuity** of weak
    solutions of divergence-form equations with **bounded measurable** coefficients, and
    the elliptic Harnack inequality in this generality (De Giorgi's iteration and/or
    Moser's). ⚠ This is *the* hard theorem of the lane, so budget for it accordingly;
    note it is **divergence-form/weak**, whereas the non-divergence analogue is
    Krylov–Safonov.

### Lane F: parabolic and evolution equations

24. **Bochner spaces and the Gelfand triple.** `L²(0,T;V)`, `H¹(0,T;V*)`, the triple
    `V ↪ H ↪ V*` (consume the Bochner integral), and the integration-by-parts/embedding
    `L²(V) ∩ H¹(V*) ↪ C([0,T];H)`.
25. **Linear parabolic existence.** The **Galerkin method**: finite-dimensional
    approximation (consume ODE existence), energy estimates, weak-compactness passage to
    the limit, giving existence/uniqueness for `∂ₜu + Lu = f`, `u(0) = u₀`. The parabolic
    maximum principle.
26. **Semigroups.** The **heat semigroup**, generators, and **Hille–Yosida**; the heat
    kernel on `ℝⁿ` (consume the Fourier transform) and the smoothing estimates.

### Stretch goals (state once the lanes above are solid)

- **Strichartz estimates** for the wave and Schrödinger equations (Tao, *Nonlinear
  Dispersive Equations*): the `TT*` method, the dispersive `L¹→L^∞` decay, and the
  endpoint Keel–Tao argument, consuming the Fourier/oscillatory-integral and
  interpolation lanes.
- **Quasilinear elliptic existence** via Schauder/Leray–Schauder fixed-point theory on top
  of Lane E (the De Giorgi–Nash–Moser a-priori estimates supply the compactness).
- **Stochastic PDE:** a result from Krylov's analytic `L_p`-theory of SPDE, or
  Da Prato–Debussche for the stochastic Navier–Stokes / 2D stochastic quantization,
  consuming the parabolic and Bochner lanes plus Mathlib's probability stack.

## Acceptance criteria ("checks along the way")

Concrete sanity checks that rule out vacuous or mis-stated definitions:

- **Spaces agree where they must:** `W^{k,2}(ℝⁿ) = H^{k,2}(ℝⁿ)` (Lane A.3) and
  `ker(trace) = W^{1,p}_0` (Lane A.6).
- **Poincaré is non-vacuous:** the constant is finite on a concrete bounded `Ω` (e.g. a
  ball) and the inequality genuinely *fails* on `ℝⁿ`. Formalize both directions so the
  hypothesis is known to be load-bearing.
- **End-to-end existence:** the Dirichlet problem `−Δu = f` in a ball, `u = 0` on the
  boundary, has a unique weak solution (Lane D.17), it is **smooth** for smooth `f`
  (Lane E.20), and it equals the **Newtonian-potential** solution (Lane C.15): three lanes
  meeting on one example.
- **Eigenvalues are real and positive:** the first Dirichlet eigenvalue of `−Δ` is
  positive (Lane D.19), matching the Poincaré constant.
- **Regularity actually upgrades:** exhibit a weak solution that is *only* `H¹` a priori
  and prove it is `C^{0,α}` (Lane E.23), the De Giorgi–Nash–Moser payoff on an example.
- **Maximum principle bites:** a subsolution of `−Δu ≤ 0` attains its max on `∂Ω`
  (Lane C.13), with a counterexample showing the sign condition is necessary.

## References

- L. C. Evans, *Partial Differential Equations*, the default modern graduate text;
  Sobolev spaces (Ch. 5), second-order elliptic (Ch. 6), parabolic/Galerkin (Ch. 7),
  semigroups (Ch. 7), Hamilton–Jacobi & conservation laws.
- D. Gilbarg, N. Trudinger, *Elliptic Partial Differential Equations of Second Order*:
  maximum principles (Ch. 3), Schauder (Ch. 6), `Lᵖ` theory (Ch. 9), De Giorgi–Nash–Moser
  (Ch. 8); the canonical elliptic reference.
- L. Grafakos, *Classical Fourier Analysis* (and *Modern*) / E. Stein, *Singular Integrals
  and Differentiability Properties of Functions*: maximal function, interpolation,
  Calderón–Zygmund, BMO. Baby versions in Stein–Shakarchi vol. 4, §3.3.
- T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*: Strichartz
  estimates and the dispersive stretch goals.
- N. V. Krylov, *An Analytic Approach to SPDEs*; G. Da Prato, A. Debussche, *Stochastic
  Navier–Stokes*: the stochastic stretch goals.
- The **Carleson project** (van Doorn–Thiele), <https://github.com/fpvandoorn/carleson>,
  the path-finding high-analysis Lean project; the source to vendor the Hardy–Littlewood
  maximal function, Vitali covering, and Calderón–Zygmund machinery from.

## How to drive it

Large by design, expanded **iteratively**. **Lane A comes first** and to a high standard,
because almost everything downstream needs `W^{k,p}(Ω)` and Rellich. Then Lanes B, C, D
can proceed largely in parallel: Lane C (potential theory) is the easiest early win and
partly exists in Mathlib already; Lane D (energy-method existence) is the shortest path to
a real PDE theorem because Lax–Milgram is *already there*; Lane B (harmonic analysis) is
the long pole that Lane E's regularity depends on. Lane E is the deep core of the
roadmap, and Lane F and the stretch goals come last. As each lane makes the next one's
*types* expressible in `TauCeti/`, state those milestones in `Targets.lean` (with
`sorry`) and hand them to the AIs to discharge. Nothing here blocks on upstream Mathlib.

## Acknowledgements

This roadmap builds directly on earlier discussions on the [Lean
Zulip](https://leanprover.zulipchat.com/), and would not have been possible without them:

- [#AI authored projects > De Giorgi–Nash–Moser](https://leanprover.zulipchat.com/#narrow/channel/583339-AI%20authored%20projects/topic/De%20Giorgi%E2%80%93Nash%E2%80%93Moser),
  the De Giorgi–Nash–Moser formalization experiment that informed this roadmap's headline
  regularity target, with Filippo A. E. Nuccio, Przemek Chojecki, and others.
- [#mathlib4 > PDE Theory](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/PDE%20Theory)
  (Anatole Dedecker, Michael Rothgang, Filippo A. E. Nuccio, Aditya Ramabadran), scoping
  the PDE theory to build on top of Mathlib's analysis stack.
- [#new members > elliptic PDEs](https://leanprover.zulipchat.com/#narrow/channel/113489-new%20members/topic/elliptic%20PDEs),
  discussing prerequisites for formalizing elliptic PDEs.

Thanks to everyone who contributed to these discussions.
