# IdxDiff — Index Differential Testing

IdxDiff is a differential testing tool for finding index-related bugs in DBMSs.

## Bug List

This section lists the bugs found by IdxDiff. Each entry includes a link to the corresponding bug report.

### MySQL Bugs

*   **[MySQL Bug #120350](https://bugs.mysql.com/bug.php?id=120350)** (Confirmed)

*   **[MySQL Bug #120352](https://bugs.mysql.com/bug.php?id=120352)** (Confirmed)

*   **[MySQL Bug #120456](https://bugs.mysql.com/bug.php?id=120456)** (Confirmed)

*   **[MySQL Bug #120475](https://bugs.mysql.com/bug.php?id=120475)** (Confirmed)

*   **[MySQL Bug #120476](https://bugs.mysql.com/bug.php?id=120476)** (Confirmed)

*   **[MySQL Bug #120491](https://bugs.mysql.com/bug.php?id=120491)** (Confirmed)

*   **[MySQL Bug #120527](https://bugs.mysql.com/bug.php?id=120527)** (Confirmed)

*   **[MySQL Bug #120539](https://bugs.mysql.com/bug.php?id=120539)** (Open)

*   **[MySQL Bug #120584](https://bugs.mysql.com/bug.php?id=120584)** (Confirmed)

*   **[MySQL Bug #120562](https://bugs.mysql.com/bug.php?id=120562)** (Confirmed, S1 Critical)

### MariaDB Bugs

*   **[MDEV-39773](https://jira.mariadb.org/browse/MDEV-39773)** (In Review, Critical)

*   **[MDEV-39823](https://jira.mariadb.org/browse/MDEV-39823)** (Confirmed)

*   **[MDEV-39853](https://jira.mariadb.org/browse/MDEV-39853)** (In Review, Critical)

*   **[MDEV-39879](https://jira.mariadb.org/browse/MDEV-39879)** (Confirmed)

*   **[MDEV-40046](https://jira.mariadb.org/browse/MDEV-40046)** (Confirmed)

### TiDB Bugs

*   **[TiDB Issue #68152](https://github.com/pingcap/tidb/issues/68152)** (Confirmed)

*   **[TiDB Issue #68428](https://github.com/pingcap/tidb/issues/68428)** (Confirmed)

*   **[TiDB Issue #68455](https://github.com/pingcap/tidb/issues/68455)** (Confirmed)

*   **[TiDB Issue #68533](https://github.com/pingcap/tidb/issues/68533)** (Confirmed, Critical)

### PolarDB-X Bugs

*   **[PolarDB-X Issue #294](https://github.com/polardb/polardbx-sql/issues/294)** (Confirmed)

*   **[PolarDB-X Issue #295](https://github.com/polardb/polardbx-sql/issues/295)** (Confirmed)

*   **[PolarDB-X Issue #296](https://github.com/polardb/polardbx-sql/issues/296)** (Confirmed)

## Quick Start

### Get the Project

```bash
# Clone from GitHub
git clone https://github.com/DiffTest/IdxDiff.git
cd IdxDiff
```

### Prerequisites

- Java 11 or higher
- Maven 3.6+

### Building

```bash
mvn clean package -DskipTests
```

### Running

After building, run idxdiff with your target database:

**Important**: General options must come **before** the database type, while database-specific options come **after**.

#### Basic Example

```bash
# General options come BEFORE the database type
java -jar target/idxdiff-*.jar \
    --num-threads 4 \
    --num-tries 100 \
    mysql \
    --oracle INDEX \
    --host localhost \
    --port 3306 \
    --username test \
    --password test
```

For the other supported databases, replace `mysql` with `mariadb`, `tidb`, or `polardb` accordingly.

Useful flags:

- `--num-tries N` — stop after N bugs.
- `--timeout-seconds S` — stop after S seconds.
- `--use-reducer` — automatic delta-debugging on a found bug.

## Supported Databases

- MySQL
- MariaDB
- TiDB
- PolarDB-X
- PostgreSQL

## Documentation
- For detailed usage instructions and advanced options, refer to the official [SQLancer documentation](https://github.com/sqlancer/sqlancer).

## Acknowledgement

IdxDiff is built on top of the [SQLancer](https://github.com/sqlancer/sqlancer) framework. SQLancer has provided an excellent foundation — many thanks to the SQLancer contributors. 